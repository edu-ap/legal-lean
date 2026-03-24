/-
  LegalLean.IR.Legal — Typed Legal Semantic Intermediate Representation.

  The IR is the structural bridge between natural language legal text and
  formal Lean 4 proofs.  It is the deposit point for the "heuristic
  transducer" (LLM) and the input consumed by the "invariant verifier"
  (Lean 4 lowering pass).

  Pipeline:  English legal text → IR.Clause → LegalLean core types

  The IR captures all 8 factors from the factorial hardening matrix:
    1. voice              — active / passive / impersonal
    2. modality           — shall / must / may / should / prohibited / none
    3. negation           — positive / negative / double_negative / none
    4. exception_structure — none / simple_proviso / nested / defeasible
    5. temporal           — present / past / conditional_future / none
    6. thresholds         — none / numeric / comparative
    7. definitions        — inline / cross_referenced / undefined
    8. cross_references   — none / intra_statute / inter_statute

  Design principles:
  - Composable: every type is a building block, not a monolith.
  - Normalisation-friendly: no implicit ordering; all list fields are
    order-independent for the purpose of normalisation.
  - Lowering-friendly: every IR node has a direct LegalLean counterpart
    or maps to FormalisationBoundary.boundary.

  Compatible with Lean 4 v4.24.0 (no Mathlib required).
-/

import LegalLean.Core

namespace LegalLean.IR

-- ============================================================
-- Factor 1: Voice
-- ============================================================

/-- Grammatical voice of a legal clause.
    Active:     "The taxpayer shall deduct..."
    Passive:    "Interest shall be deducted by..."
    Impersonal: "No deduction is allowed..."
    Normalisation target: always lower to Active. -/
inductive Voice where
  | active
  | passive
  | impersonal
  deriving Repr, BEq, DecidableEq, Inhabited

-- ============================================================
-- Factor 2: Modality
-- ============================================================

/-- Deontic and epistemic modalities as they appear in legal text.
    Maps to LegalLean.Deontic for lowering:
      - shall / must / obligatory → Deontic.obligatory
      - may                       → Deontic.permitted
      - prohibited / mustNot      → Deontic.prohibited
      - should                    → Deontic.permitted (with lower priority)
      - none                      → Deontic.permitted (default) -/
inductive Modality where
  | shall          -- strong obligation: "the taxpayer shall..."
  | must           -- strong obligation: "must be secured by..."
  | may            -- permission: "may deduct..."
  | should         -- weak obligation / recommendation
  | mustNot        -- explicit prohibition: "must not..."
  | prohibited     -- passive prohibition: "no deduction shall be allowed"
  | none           -- no explicit modality present
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Canonical lowering of IR.Modality to LegalLean.Deontic.
    `should` maps to permitted (weaker than obligatory). -/
def Modality.toDeontic : Modality → LegalLean.Deontic
  | .shall     => .obligatory
  | .must      => .obligatory
  | .may       => .permitted
  | .should    => .permitted
  | .mustNot   => .prohibited
  | .prohibited => .prohibited
  | .none      => .permitted

-- ============================================================
-- Factor 3: Negation
-- ============================================================

/-- Polarity of a clause: how negation is expressed. -/
inductive Negation where
  | positive        -- affirmative: "interest IS deductible"
  | negative        -- simple negation: "interest is NOT deductible"
  | doubleNegative  -- double-negative: "no deduction shall be disallowed"
  | none            -- negation not applicable (e.g. definition)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Normalise double negatives to positive (semantic equivalence). -/
def Negation.normalise : Negation → Negation
  | .doubleNegative => .positive
  | other           => other

-- ============================================================
-- Factor 4: Exception structure
-- ============================================================

/-- A reference to an exception: either a proviso clause, a nested
    exception, or a defeating rule.  Identified by string ID so that
    exception structures can be composed and resolved. -/
structure ExceptionRef where
  /-- ID of the clause or rule that constitutes the exception. -/
  clauseId : String
  /-- Human-readable description of the exception. -/
  description : String
  deriving Repr, BEq

/-- Exception structure of a clause.  Defeasible exceptions are those
    whose defeating clause can itself be defeated (R3 defeats E1.1). -/
inductive ExceptionStructure where
  | none
  /-- "Except as provided in subsection X..." — one proviso. -/
  | simpleProviso (proviso : ExceptionRef)
  /-- Proviso with its own sub-exceptions (deeply nested). -/
  | nested (outer : ExceptionRef) (inner : List ExceptionRef)
  /-- Default-logic defeat: higher-priority rule can retract conclusion. -/
  | defeasible (defeaters : List ExceptionRef)
  deriving Repr

/-- Flatten a nested exception to a list of all exception refs.
    Used during normalisation to compute the full defeater set. -/
def ExceptionStructure.allRefs : ExceptionStructure → List ExceptionRef
  | .none                    => []
  | .simpleProviso p         => [p]
  | .nested outer inner      => outer :: inner
  | .defeasible defeaters    => defeaters

-- ============================================================
-- Factor 5: Temporal constraint
-- ============================================================

/-- Temporal tense / aspect of a legal clause.
    ConditionalFuture captures "if X occurs on date Y, then..."
    Past captures grandfather / historical provisions. -/
inductive TemporalTense where
  | present           -- current obligation / permission
  | past              -- historical fact or grandfathered condition
  | conditionalFuture -- "if taxable year begins after..."
  | none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A temporal constraint on when a clause is operative. -/
inductive TemporalConstraint where
  | unconstrained
  /-- Operative only for dates on or after cutoff. -/
  | onOrAfter (cutoff : LegalLean.Date)
  /-- Operative only for dates on or before cutoff. -/
  | onOrBefore (cutoff : LegalLean.Date)
  /-- Operative for dates strictly between lo and hi. -/
  | between (lo hi : LegalLean.Date)
  /-- Operative only when a named condition holds (open texture). -/
  | conditional (description : String)
  deriving Repr

-- ============================================================
-- Factor 6: Numeric thresholds
-- ============================================================

/-- The kind of numeric threshold in a clause. -/
inductive ThresholdKind where
  | none
  /-- Exact ceiling / floor: "not more than $750,000" -/
  | numeric (amount : Nat) (unit : String)
  /-- Comparative: "greater than", "equal to or less than" -/
  | comparative (relation : String) (referent : String)
  deriving Repr, BEq

-- ============================================================
-- Factor 7: Definition provenance
-- ============================================================

/-- How a key term is defined within the clause or its context. -/
inductive DefinitionKind where
  /-- Defined inline: "For purposes of this subsection, 'X' means Y." -/
  | inline (text : String)
  /-- Defined by cross-reference: "as defined in §163(h)(4)(A)" -/
  | crossReferenced (ref : String) (text : String)
  /-- Not defined: relies on common law / vague usage. -/
  | undefined (term : String)
  deriving Repr, BEq

-- ============================================================
-- Factor 8: Cross-references
-- ============================================================

/-- The scope of a cross-reference. -/
inductive CrossRefScope where
  | none
  /-- Within the same statute / section. -/
  | intraStatute (target : String)
  /-- To a different statute entirely. -/
  | interStatute (statute : String) (target : String)
  deriving Repr, BEq

-- ============================================================
-- Actors / Entities
-- ============================================================

/-- Actor kind: who bears the right, duty, or liability. -/
inductive ActorKind where
  | naturalPerson
  | legalPerson       -- corporation, trust, partnership
  | authority         -- IRS, USCIS, ACCC, etc.
  | instrument        -- statute, regulation, contract
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A typed actor in the legal IR. -/
structure Actor where
  id         : String
  name       : String
  kind       : ActorKind
  /-- Source text from which this actor was extracted. -/
  sourceText : String
  deriving Repr

-- ============================================================
-- Vagueness marker (FormalisationBoundary at IR level)
-- ============================================================

/-- Marks where the IR cannot resolve semantics and formal
    verification must yield to human judgment.
    This is the IR-level analogue of FormalisationBoundary. -/
inductive VaguenessMarker where
  /-- Fully formalisable: no open texture present. -/
  | precise
  /-- Hart's penumbra: core meaning is clear, edge cases are not.
      `core` and `penumbra` describe the settled and contested regions. -/
  | vague (term : String) (core : String) (penumbra : String)
  /-- Discretionary: an authority has power to decide. -/
  | discretionary (term : String) (authority : String) (scope : String)
  /-- Ambiguous: multiple plausible interpretations. -/
  | ambiguous (term : String) (interpretations : List String)
  deriving Repr

-- ============================================================
-- Core IR type: Clause
-- ============================================================

/-- A Legal IR Clause: the central composable unit.

    A Clause is a single normative sentence or proposition extracted
    from legal text, annotated with all 8 factorial-hardening factors.
    Clauses compose to form a Provision, which composes to form a Statute.

    All fields correspond to exactly one factor in the coverage matrix:
      voice             → Factor 1
      modality          → Factor 2
      negation          → Factor 3
      exceptionStructure → Factor 4
      temporalTense     → Factor 5 (tense annotation)
      temporalConstraint → Factor 5 (operative window)
      threshold         → Factor 6
      definitions       → Factor 7
      crossRefs         → Factor 8

    Plus semantic content: actors, predicate, vaguenessMarker. -/
structure Clause where
  /-- Unique ID within the IR document (e.g. "IRC163h-C1"). -/
  id                : String
  /-- The original English source text. -/
  sourceText        : String
  /-- Subject: the actor bearing the right/duty. -/
  subject           : Actor
  /-- The predicate (action or state) the clause asserts. -/
  predicate         : String
  /-- Object / direct object of the predicate, if present. -/
  object            : Option String
  -- Factor 1
  voice             : Voice
  -- Factor 2
  modality          : Modality
  -- Factor 3
  negation          : Negation
  -- Factor 4
  exceptionStructure : ExceptionStructure
  -- Factor 5
  temporalTense     : TemporalTense
  temporalConstraint : TemporalConstraint
  -- Factor 6
  threshold         : ThresholdKind
  -- Factor 7
  definitions       : List DefinitionKind
  -- Factor 8
  crossRefs         : List CrossRefScope
  /-- Vagueness annotation: where does human judgment enter? -/
  vaguenessMarker   : VaguenessMarker
  /-- Priority level for defeat-resolution (higher = stronger). -/
  priority          : Nat
  /-- Optional source section reference (e.g. "26 U.S.C. §163(h)(1)"). -/
  sourceRef         : Option String
  deriving Repr

-- ============================================================
-- Provision: a group of Clauses from one statutory subsection
-- ============================================================

/-- A legal provision: a collection of clauses from one subsection. -/
structure Provision where
  id       : String
  title    : String
  clauses  : List Clause
  deriving Repr

-- ============================================================
-- IR Document: top-level unit
-- ============================================================

/-- A complete IR document: the structured output of the transducer. -/
structure IRDocument where
  /-- Human-readable title (e.g. "IRC §163(h)"). -/
  title      : String
  /-- Source citation. -/
  sourceRef  : String
  provisions : List Provision
  /-- Proportion of clauses with VaguenessMarker.precise (0.0–1.0). -/
  formalisabilityRatio : Float
  deriving Repr

end LegalLean.IR
