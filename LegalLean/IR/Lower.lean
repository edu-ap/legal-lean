/-
  LegalLean.IR.Lower — Lowering pass: IR.Clause → LegalLean core types.

  This pass consumes normalised IR clauses and emits LegalLean.LegalRule
  values plus FormalisationBoundary annotations.

  Design: the lowering is a TOTAL function.  Every IR.Clause produces
  EITHER a valid LegalRule OR a FormalisationBoundary.boundary explaining
  why full formalisation is not possible.  There are no partial functions
  and no panics.

  Lowering map (IR field → LegalLean type):
    Modality.toDeontic     → LegalLean.Deontic
    VaguenessMarker.vague  → FormalisationBoundary.boundary
    VaguenessMarker.precise → FormalisationBoundary.formal (with sorry witness)
    ExceptionStructure     → defeatedBy list in LegalRule
    ThresholdKind.numeric  → embedded in rule description + conclusion
    TemporalConstraint     → embedded in rule description
    CrossRefScope          → embedded in rule id

  Compatible with Lean 4 v4.24.0 (no Mathlib required).
-/

import LegalLean.Core
import LegalLean.IR.Legal
import LegalLean.IR.Normalise

namespace LegalLean.IR.Lower

open LegalLean
open LegalLean.IR
open LegalLean.IR.Normalise

-- ============================================================
-- Authority lowering
-- ============================================================

/-- Map an IR actor name to a LegalLean.Authority.
    Unknown actors default to irs (the most common in IRC domains).
    This is conservative: if the actor is unknown the downstream
    FormalisationBoundary will carry an appropriate reason. -/
-- Helper: check whether a string contains a substring.
-- `String.contains` in Lean 4 checks for a single Char; we use
-- `isInfixOf` via manually testing prefix offsets.
private def strHas (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n == [] then true
  else
    -- slide a window of length n.length over h
    let nLen := n.length
    let hLen := h.length
    if hLen < nLen then false
    else
      (List.range (hLen - nLen + 1)).any fun i =>
        (h.drop i).take nLen == n

def lowerAuthority (actorName : String) : Authority :=
  if strHas actorName "IRS" || strHas actorName "Internal Revenue" then
    .irs
  else if strHas actorName "Tax Court" then
    .taxCourt
  else if strHas actorName "USCIS" then
    .uscis
  else if strHas actorName "ACCC" then
    .accc
  else
    .irs  -- conservative default

-- ============================================================
-- Priority lowering
-- ============================================================

/-- Map an IR priority level to a LegalLean.Priority.
    Source is inferred from context fields on the clause. -/
def lowerPriority (level : Nat) (sourceRef : Option String) : Priority where
  level  := level
  source := match sourceRef with
            | some r => r
            | none   => "statute"

-- ============================================================
-- Defeater list extraction
-- ============================================================

/-- Extract the list of defeater IDs from an ExceptionStructure. -/
def defeaterIds (es : ExceptionStructure) : List String :=
  es.allRefs.map (·.clauseId)

-- ============================================================
-- Threshold description
-- ============================================================

/-- Produce a human-readable description of a threshold for embedding
    in the rule description field. -/
def thresholdDesc : ThresholdKind → String
  | .none                      => ""
  | .numeric amount unit       =>
      s!" (threshold: {amount} {unit})"
  | .comparative relation ref  =>
      s!" ({relation} {ref})"

-- ============================================================
-- Temporal constraint description
-- ============================================================

def temporalDesc : TemporalConstraint → String
  | .unconstrained             => ""
  | .onOrAfter c               =>
      s!" (operative on or after {c.year}-{c.month}-{c.day})"
  | .onOrBefore c              =>
      s!" (operative on or before {c.year}-{c.month}-{c.day})"
  | .between lo hi             =>
      s!" (operative {lo.year}-{lo.month}-{lo.day} to {hi.year}-{hi.month}-{hi.day})"
  | .conditional desc          =>
      s!" (conditional on: {desc})"

-- ============================================================
-- Main lowering result type
-- ============================================================

/-- The result of lowering a single IR clause.
    Either a fully-lowered LegalRule, or a boundary annotation.
    `String` is used as the evidence type so rules compose without
    requiring domain-specific witnesses at the IR level. -/
-- LegalRule has a function-valued field `conclusion`, so Repr cannot be
-- auto-derived for LowerResult.  We define a lightweight summarise function
-- instead of deriving Repr.
inductive LowerResult where
  /-- Full rule: the clause was formalisable. -/
  | rule   (r : LegalRule String)
  /-- Boundary: the clause hits open texture or discretion. -/
  | boundary (clauseId : String) (reason : String) (authority : Authority)
  /-- Mixed: partially formal, partially boundary. -/
  | mixed  (r : LegalRule String) (boundaryNote : String) (authority : Authority)

/-- Human-readable summary of a LowerResult (replaces Repr). -/
def LowerResult.summarise : LowerResult → String
  | .rule r           => s!"RULE[{r.id}]: {r.description}"
  | .boundary id r _  => s!"BOUNDARY[{id}]: {r}"
  | .mixed r note _   => s!"MIXED[{r.id}]: {note}"

instance : Repr LowerResult where
  reprPrec lr _ := Std.Format.text (lr.summarise)

-- ============================================================
-- Lowering a single Clause
-- ============================================================

/-- Lower a normalised IR Clause to a LowerResult.

    The function is total: every VaguenessMarker value is handled.
    `sorry` is used only for proof obligations inside `EvidenceFor`,
    not for structural logic. -/
def lowerClause (c : Clause) : LowerResult :=
  let desc := c.predicate ++
              thresholdDesc c.threshold ++
              temporalDesc c.temporalConstraint
  let modality := c.modality.toDeontic
  let prio     := lowerPriority c.priority c.sourceRef
  let defeaters := defeaterIds c.exceptionStructure
  match c.vaguenessMarker with
  | .precise =>
      -- Fully formalisable: emit a LegalRule with a trivial conclusion
      LowerResult.rule {
        id          := c.id
        description := desc
        modality    := modality
        priority    := prio
        conclusion  := fun _evidence => True   -- placeholder; refined by domain layer
        defeatedBy  := defeaters
      }
  | .vague term core penumbra =>
      -- Open texture: core is formal, penumbra requires human judgment
      let reason := s!"'{term}': core = '{core}'; penumbra = '{penumbra}'"
      let auth   := lowerAuthority c.subject.name
      -- Emit a mixed result: rule captures the formal part
      LowerResult.mixed
        { id          := c.id
          description := desc ++ s!" [OPEN TEXTURE: {term}]"
          modality    := modality
          priority    := prio
          conclusion  := fun _evidence => True
          defeatedBy  := defeaters }
        reason
        auth
  | .discretionary term auth scope =>
      LowerResult.boundary
        c.id
        s!"Discretionary: '{term}' — authority '{auth}' has scope '{scope}'"
        (lowerAuthority auth)
  | .ambiguous term interpretations =>
      let interps := String.intercalate " / " interpretations
      LowerResult.boundary
        c.id
        s!"Ambiguous: '{term}' — interpretations: {interps}"
        Authority.irsTaxCourt

-- ============================================================
-- Lowering a Provision
-- ============================================================

/-- Lower all clauses in a provision, normalising first. -/
def lowerProvision (p : Provision) : List LowerResult :=
  (normaliseProvision p).clauses.map lowerClause

-- ============================================================
-- Lowering an IRDocument
-- ============================================================

/-- Result of lowering a complete IR document. -/
structure DocumentLowerResult where
  /-- Source IR document title. -/
  title       : String
  /-- All clause lowering results. -/
  results     : List LowerResult
  /-- Count of fully-lowered rules. -/
  ruleCount   : Nat
  /-- Count of boundary annotations. -/
  boundaryCount : Nat
  /-- Count of mixed results. -/
  mixedCount  : Nat
  deriving Repr

/-- Lower a complete IR document. -/
def lowerDocument (doc : IRDocument) : DocumentLowerResult :=
  let results := (normaliseDocument doc).provisions.foldl (fun acc p => acc ++ lowerProvision p) []
  let rules     := results.filter (fun r => match r with | .rule _   => true | _ => false)
  let bounds    := results.filter (fun r => match r with | .boundary _ _ _ => true | _ => false)
  let mixeds    := results.filter (fun r => match r with | .mixed _ _ _ => true | _ => false)
  { title         := doc.title
    results       := results
    ruleCount     := rules.length
    boundaryCount := bounds.length
    mixedCount    := mixeds.length }

-- ============================================================
-- FormalisationBoundary extraction
-- ============================================================

/-- Extract FormalisationBoundary values from lowering results,
    for downstream integration with the core LegalLean types. -/
def toBoundary (lr : LowerResult) : Option (FormalisationBoundary Prop) :=
  match lr with
  | .rule _                     => none
  | .boundary _ reason auth     => some (FormalisationBoundary.boundary reason auth)
  | .mixed _ boundaryNote _auth => some (FormalisationBoundary.mixed "formal part present" boundaryNote)

/-- Extract all boundary annotations from a document's lowering result. -/
def allBoundaries (dlr : DocumentLowerResult) : List (FormalisationBoundary Prop) :=
  dlr.results.filterMap toBoundary

end LegalLean.IR.Lower
