/-
  LegalLean.Core — Foundation types for verified legal reasoning.

  Architecture: LLMs are heuristic transducers (messy input → structured form);
  Lean 4 is the invariant verifier (checks the logic).

  Key types:
  - `Date`: ISO 8601 calendar date with proper ordering
  - `Authority`: typed enumeration of adjudicatory authorities
  - `Deontic`: permitted / prohibited / obligatory
  - `LegalRule`: a rule with defeasibility metadata
  - `EvidenceFor`: propositions-as-types for legal evidence
  - `FormalisationBoundary`: Hart's open texture as a first-class type

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
-/

namespace LegalLean

-- ============================================================
-- Date: proper calendar date with structural ordering
-- ============================================================

/-- A calendar date with year, month, and day components.
    ISO 8601 representation: YYYY-MM-DD.
    Ordering is lexicographic over (year, month, day) triples,
    which is total and coincides with chronological order. -/
structure Date where
  year  : Nat
  month : Nat  -- 1–12
  day   : Nat  -- 1–31
  deriving Repr, BEq, DecidableEq

/-- Lexicographic ordering on `Date`, lifting the natural number ordering
    via the triple (year, month, day).  This is a total preorder [reflexive,
    transitive, total] and a partial order [additionally antisymmetric] since
    the components are all `Nat`. -/
instance : LE Date where
  le a b := a.year < b.year ∨
            (a.year = b.year ∧ a.month < b.month) ∨
            (a.year = b.year ∧ a.month = b.month ∧ a.day ≤ b.day)

instance : LT Date where
  lt a b := a.year < b.year ∨
            (a.year = b.year ∧ a.month < b.month) ∨
            (a.year = b.year ∧ a.month = b.month ∧ a.day < b.day)

/-- Decidability of `Date` comparison. Allows `if d1 ≤ d2 then ...` in defs. -/
instance decLeDate (a b : Date) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable
    (a.year < b.year ∨
     (a.year = b.year ∧ a.month < b.month) ∨
     (a.year = b.year ∧ a.month = b.month ∧ a.day ≤ b.day)))

-- ============================================================
-- Authority: typed enumeration of adjudicatory authorities
-- ============================================================

/-- The adjudicatory authorities referenced across the case studies.
    Replacing magic strings with a closed inductive eliminates typos and
    makes authority references machine-checkable. -/
inductive Authority where
  /-- Internal Revenue Service (US federal tax authority). -/
  | irs          : Authority
  /-- US Tax Court (federal judicial tribunal for tax disputes). -/
  | taxCourt     : Authority
  /-- IRS and Tax Court jointly (common in IRC §163(h) open texture). -/
  | irsTaxCourt  : Authority
  /-- US Citizenship and Immigration Services. -/
  | uscis        : Authority
  /-- Australian Competition and Consumer Commission. -/
  | accc         : Authority
  /-- Telecommunications Industry Ombudsman (Australia). -/
  | tio          : Authority
  /-- ACCC and TIO jointly (common in TCP Code open texture). -/
  | acccTio      : Authority
  /-- ACCC, TIO, and courts collectively. -/
  | acccTioCourt : Authority
  /-- Provider self-determination, subject to ACCC audit. -/
  | providerAcccc : Authority
  /-- Provider initial determination, reviewable by ACCC. -/
  | providerAcccc2 : Authority
  deriving Repr, BEq, DecidableEq, Inhabited

-- ============================================================
-- Deontic modalities
-- ============================================================

/-- Deontic modalities: the three fundamental normative positions. -/
inductive Deontic where
  | permitted    : Deontic
  | prohibited   : Deontic
  | obligatory   : Deontic
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A legal rule's priority level for defeat resolution. -/
structure Priority where
  level : Nat
  source : String  -- e.g. "statute", "regulation", "contract", "precedent"
  deriving Repr, BEq

/-- A legal rule with defeasibility metadata.
    Rules can be defeated by higher-priority rules or new evidence.
    This is the core of non-monotonic legal reasoning.

    Note: no `deriving` — contains function-valued field `conclusion`. -/
structure LegalRule (α : Type) where
  id : String
  description : String
  modality : Deontic
  priority : Priority
  /-- The proposition this rule establishes, given evidence of type α. -/
  conclusion : α → Prop
  /-- Conditions under which this rule is defeated. -/
  defeatedBy : List String  -- IDs of rules that can defeat this one
  /-- Guard predicate: whether this rule is applicable to the given facts.
      Defaults to `fun _ => true` (universally applicable) so all existing
      rule definitions compile unchanged.
      Use this to gate temporal or contextual rules — e.g. a post-TCJA
      prohibition is only applicable when `year >= 2018`. -/
  applicable : α → Bool := fun _ => true

/-- Evidence for a legal proposition.
    Propositions-as-types: if you can construct an `EvidenceFor P`,
    then P is established (subject to defeasibility).

    Note: no `deriving` — contains Prop-valued field `witness`. -/
structure EvidenceFor (P : Prop) where
  source : String           -- provenance: "statute", "testimony", "document", etc.
  artifact : Option String  -- reference to supporting document/record
  /-- The actual proof witness. -/
  witness : P

/-
  FormalisationBoundary — The intellectually novel contribution.

  Hart's "open texture" (The Concept of Law, 1961): legal concepts have a
  core of settled meaning and a penumbra of uncertainty. Prior work (DDL,
  Catala, L4L, LegalRuleML) treats this as an external limitation on
  formalisation. We encode it WITHIN the type system.

  `RequiresHumanDetermination` is a typeclass marking propositions where
  formal verification must yield to human judgment. Subclasses distinguish:
  - `Vague`: the concept has a core/penumbra distinction (e.g. "reasonable")
  - `Discretionary`: an authority has discretion to decide (e.g. USCIS adjudicator)
-/

/-- Typeclass marking propositions that require human determination.
    Any proposition `P` with this instance cannot be fully machine-verified. -/
class RequiresHumanDetermination (P : Prop) where
  reason : String
  /-- Which authority or role must make this determination. -/
  authority : Authority

/-- Vague concepts: core cases are clear, penumbral cases are not.
    Example: "extraordinary ability" in O-1 visa criteria. -/
class Vague (P : Prop) extends RequiresHumanDetermination P where
  /-- Description of the settled core meaning. -/
  core : String
  /-- Description of the penumbral (contested) region. -/
  penumbra : String

/-- Discretionary determinations: an authority has power to decide.
    Example: USCIS adjudicator deciding "comparable evidence" under O-1. -/
class Discretionary (P : Prop) extends RequiresHumanDetermination P where
  /-- The scope of discretion granted. -/
  scope : String
  /-- Constraints on the exercise of discretion (if any). -/
  constraints : List String

/-- The formalisation boundary itself: wraps a proposition with metadata
    about whether it is fully formalisable, vague, or discretionary. -/
inductive FormalisationBoundary (P : Sort _) where
  /-- Fully formalisable: can be verified by the type checker alone. -/
  | formal (proof : P) : FormalisationBoundary P
  /-- Requires human determination: annotated with why and which authority. -/
  | boundary (reason : String) (authority : Authority) : FormalisationBoundary P
  /-- Mixed: partially formal, partially human. The `formalPart` is verified;
      the `humanPart` is annotated. -/
  | mixed (formalPart : String) (humanPart : String) : FormalisationBoundary P

end LegalLean
