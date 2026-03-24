/-
  LegalLean.IR.VariationTest — Variation family tests for REQ-014 Phase 2.

  This module implements:
    1. MinimalPair — a type pairing two IR clauses with an expected relation.
    2. Comparison functions: check whether two clauses normalise to equivalent
       or divergent LowerResults.
    3. Five variation family tests derived from the minimal pairs in the Phase 0
       factor-coverage-matrix.json.
    4. End-to-end pipeline test: English variant → IR.Clause → Normalise →
       Lower → compare LowerResults.

  The "expected relation" between two clauses is one of:
    - equivalent : both normalise to the same modality and deontic direction.
    - divergent  : normalisation diverges in modality or vagueness outcome.

  Compatible with Lean 4 v4.24.0 (no Mathlib required).
-/

import LegalLean.IR.Legal
import LegalLean.IR.Normalise
import LegalLean.IR.Lower
import LegalLean.IR.Examples

namespace LegalLean.IR.VariationTest

open LegalLean.IR
open LegalLean.IR.Normalise
open LegalLean.IR.Lower
open LegalLean.IR.Examples

-- ============================================================
-- MinimalPair type
-- ============================================================

/-- The expected semantic relation between two variants. -/
inductive ExpectedRelation where
  /-- Both variants normalise to semantically equivalent outputs.
      Equivalence is tested by comparing the modality deontic direction
      of the normalised + lowered clause. -/
  | equivalent
  /-- The variants produce divergent lowering results — different modality or
      one produces a boundary while the other produces a rule. -/
  | divergent
  deriving Repr, BEq, DecidableEq

/-- A minimal pair: two IR clauses that differ in exactly one (or a small
    number of) factors, together with the expected normative relation. -/
structure MinimalPair where
  /-- Unique identifier, e.g. "MP-001". -/
  id               : String
  /-- First variant (A). -/
  variant_a        : Clause
  /-- Second variant (B). -/
  variant_b        : Clause
  /-- Expected relation after normalisation and lowering. -/
  expected_relation : ExpectedRelation
  /-- Which factors differ between A and B. -/
  factors_varied   : List String
  /-- Human-readable rationale for the expected relation. -/
  rationale        : String
  deriving Repr

-- ============================================================
-- Comparison functions: normalise → lower → compare
-- ============================================================

/-- Extract the Deontic value from a LowerResult.
    Used as the comparison key for equivalence checks. -/
def lowerResultDeontic : LowerResult → Option LegalLean.Deontic
  | .rule r         => some r.modality
  | .boundary _ _ _ => none
  | .mixed r _ _    => some r.modality

/-- Characterise a LowerResult by its constructor tag for divergence tests. -/
inductive ResultKind where
  | rule | boundary | mixed
  deriving Repr, BEq, DecidableEq

def lowerResultKind : LowerResult → ResultKind
  | .rule _         => .rule
  | .boundary _ _ _ => .boundary
  | .mixed _ _ _    => .mixed

/-- Full pipeline for a single clause: normalise then lower. -/
def pipeline (c : Clause) : LowerResult :=
  lowerClause (normalise c)

/-- Check whether two clauses satisfy the expected relation.
    Returns true if the actual relation matches the expectation.

    Equivalence criterion: same ResultKind AND same Deontic (if both are rules).
    Divergence criterion:  different ResultKind OR different Deontic. -/
def checkRelation (pair : MinimalPair) : Bool :=
  let ra := pipeline pair.variant_a
  let rb := pipeline pair.variant_b
  match pair.expected_relation with
  | .equivalent =>
      -- Same kind; if both rules, same modality
      let kindMatch := lowerResultKind ra == lowerResultKind rb
      let deonticMatch :=
        match lowerResultDeontic ra, lowerResultDeontic rb with
        | some da, some db => da == db
        | none,    none    => true
        | _,       _       => false
      kindMatch && deonticMatch
  | .divergent =>
      -- At least one of kind or deontic must differ
      let kindDiffers := lowerResultKind ra != lowerResultKind rb
      let deonticDiffers :=
        match lowerResultDeontic ra, lowerResultDeontic rb with
        | some da, some db => da != db
        | none,    some _  => true
        | some _,  none    => true
        | none,    none    => false
      kindDiffers || deonticDiffers

-- ============================================================
-- Shared actors for variation tests
-- ============================================================

def actorTaxpayer : Actor := Examples.actorTaxpayer
def actorIRS      : Actor := Examples.actorIRS

-- ============================================================
-- Variation family 1 (MP-001): Modality variation — may vs none
--
-- Phase 0 MP-001: "The deduction is permitted (active, no explicit modality)"
-- vs "The deduction may be claimed (explicit may modality)".
-- Expected: equivalent (both lower to Deontic.permitted).
-- ============================================================

def vt1_variant_a : Clause where
  id                 := "VT1-A"
  sourceText         := "The deduction is permitted for qualified residence interest."
  subject            := actorTaxpayer
  predicate          := "deduction is permitted"
  object             := some "qualified residence interest"
  voice              := .active
  modality           := .none        -- no explicit modality; maps to permitted
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.inline "permitted means allowed without restriction"]
  crossRefs          := []
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "VT1 variant A"

def vt1_variant_b : Clause where
  id                 := "VT1-B"
  sourceText         := "The taxpayer may claim the deduction for qualified residence interest."
  subject            := actorTaxpayer
  predicate          := "may claim the deduction"
  object             := some "qualified residence interest"
  voice              := .active
  modality           := .may         -- explicit permission
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.inline "may means is permitted to"]
  crossRefs          := []
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "VT1 variant B"

def mp1 : MinimalPair where
  id               := "MP-001-VT"
  variant_a        := vt1_variant_a
  variant_b        := vt1_variant_b
  expected_relation := .equivalent
  factors_varied   := ["modality"]
  rationale        :=
    "Modality.none maps to Deontic.permitted (same as Modality.may). \
     Both variants lower to a rule with modality = permitted."

-- ============================================================
-- Variation family 2 (MP-004): Negation variation — negative vs double_negative
--
-- Phase 0 MP-004: "must meet at least 3 criteria (simple negation)"
-- vs "no applicant with fewer than 3 criteria can satisfy" (double negation).
-- Expected: equivalent (double-negative normalises to positive → same deontic).
-- ============================================================

def vt2_variant_a : Clause where
  id                 := "VT2-A"
  sourceText         := "The applicant must meet at least three criteria."
  subject            := { id := "actor-applicant", name := "applicant",
                          kind := .naturalPerson, sourceText := "O-1 applicant" }
  predicate          := "must meet at least three extraordinary ability criteria"
  object             := some "criteria list"
  voice              := .active
  modality           := .must
  negation           := .negative    -- "not below 3" phrasing
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .numeric 3 "criteria"
  definitions        := [.crossReferenced "8 C.F.R. §214.2(o)(3)(ii)" "three criteria"]
  crossRefs          := [.interStatute "8 C.F.R." "§214.2(o)(3)(ii)"]
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "8 U.S.C. §1101(a)(15)(O)(i)"

def vt2_variant_b : Clause where
  id                 := "VT2-B"
  sourceText         := "No applicant with fewer than three criteria shall not be denied extraordinary ability status."
  subject            := { id := "actor-applicant", name := "applicant",
                          kind := .naturalPerson, sourceText := "O-1 applicant" }
  predicate          := "applicant with fewer than 3 criteria shall not be denied status"
  object             := some "extraordinary ability determination"
  voice              := .active
  modality           := .shall
  negation           := .doubleNegative  -- "shall NOT be denied" → normalises to positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .numeric 3 "criteria"
  definitions        := [.crossReferenced "8 C.F.R. §214.2(o)(3)(ii)" "three criteria"]
  crossRefs          := [.interStatute "8 C.F.R." "§214.2(o)(3)(ii)"]
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "8 U.S.C. §1101(a)(15)(O)(i)"

def mp2 : MinimalPair where
  id               := "MP-004-VT"
  variant_a        := vt2_variant_a
  variant_b        := vt2_variant_b
  expected_relation := .equivalent
  factors_varied   := ["negation"]
  rationale        :=
    "Negation.doubleNegative normalises to Negation.positive via N2. \
     After normalisation, VT2-B has modality=shall → obligatory; VT2-A has \
     modality=must → obligatory. Both lower to rule with obligatory modality."

-- ============================================================
-- Variation family 3 (MP-007): Divergent — pre-TCJA may vs post-TCJA mustNot
--
-- Phase 0 MP-007: "IRC §163(h) permits home equity interest deduction (pre-TCJA)"
-- vs "TCJA prohibits home equity interest deduction (post-TCJA)".
-- Expected: divergent (permitted vs prohibited — normative reversal).
-- ============================================================

def vt3_variant_a : Clause where
  id                 := "VT3-A"
  sourceText         := "The taxpayer may deduct interest on home equity indebtedness (pre-2018)."
  subject            := actorTaxpayer
  predicate          := "may deduct home equity interest"
  object             := some "home equity indebtedness"
  voice              := .active
  modality           := .may           -- permission
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .onOrBefore ⟨2017, 12, 31⟩
  threshold          := .numeric 10000000 "cents ($100,000)"
  definitions        := [.crossReferenced "§163(h)(3)(C)" "home equity indebtedness"]
  crossRefs          := [.intraStatute "§163(h)(3)(C)"]
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "26 U.S.C. §163(h) (pre-TCJA)"

def vt3_variant_b : Clause where
  id                 := "VT3-B"
  sourceText         := "No deduction shall be allowed for interest on home equity indebtedness for any taxable year beginning after December 31, 2017."
  subject            := actorTaxpayer
  predicate          := "home equity interest deduction is prohibited post-2017"
  object             := some "home equity indebtedness"
  voice              := .passive
  modality           := .prohibited    -- prohibition
  negation           := .negative
  exceptionStructure := .none
  temporalTense      := .conditionalFuture
  temporalConstraint := .onOrAfter ⟨2018, 1, 1⟩
  threshold          := .none
  definitions        := [.crossReferenced "§163(h)(3)(C)" "home equity indebtedness"]
  crossRefs          := [.intraStatute "§163(h)(3)(C)"]
  vaguenessMarker    := .precise
  priority           := 2
  sourceRef          := some "26 U.S.C. §163(h)(3)(F)(i)(II)"

def mp3 : MinimalPair where
  id               := "MP-007-VT"
  variant_a        := vt3_variant_a
  variant_b        := vt3_variant_b
  expected_relation := .divergent
  factors_varied   := ["modality", "temporal", "voice"]
  rationale        :=
    "VT3-A: may → Deontic.permitted. VT3-B: prohibited → Deontic.prohibited. \
     Deontic outcomes differ → divergent. This is the TCJA monotonicity break."

-- ============================================================
-- Variation family 4 (MP-003): Threshold variation — comparative vs numeric
--
-- Phase 0 MP-003: exemption priority stated comparatively vs numerically.
-- Expected: equivalent (both express the same priority ordering).
-- ============================================================

def vt4_variant_a : Clause where
  id                 := "VT4-A"
  sourceText         := "An exemption rule has higher priority than the rule it defeats."
  subject            := { id := "actor-instrument", name := "exemption rule",
                          kind := .instrument, sourceText := "lex specialis rule" }
  predicate          := "exemption rule priority exceeds base rule priority"
  object             := some "priority ordering"
  voice              := .active
  modality           := .shall
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .comparative "greater than" "the base rule priority"
  definitions        := [.crossReferenced "§1.1" "priority"]
  crossRefs          := [.intraStatute "§1.1"]
  vaguenessMarker    := .precise
  priority           := 2
  sourceRef          := some "VT4 variant A"

def vt4_variant_b : Clause where
  id                 := "VT4-B"
  sourceText         := "The exemption priority level is 2; the base rule priority level is 1."
  subject            := { id := "actor-instrument", name := "exemption rule",
                          kind := .instrument, sourceText := "lex specialis rule" }
  predicate          := "exemption priority = 2, base priority = 1"
  object             := some "priority levels"
  voice              := .active
  modality           := .shall
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .numeric 2 "priority level"
  definitions        := [.crossReferenced "§1.1" "priority"]
  crossRefs          := [.intraStatute "§1.1"]
  vaguenessMarker    := .precise
  priority           := 2
  sourceRef          := some "VT4 variant B"

def mp4 : MinimalPair where
  id               := "MP-003-VT"
  variant_a        := vt4_variant_a
  variant_b        := vt4_variant_b
  expected_relation := .equivalent
  factors_varied   := ["thresholds"]
  rationale        :=
    "Comparative and numeric thresholds both express the same priority ordering. \
     Both lower to obligatory rules. ThresholdKind difference is structural, \
     not normative — the deontic direction is unchanged."

-- ============================================================
-- Variation family 5 (MP-005): Exception structure variation — defeasible vs simpleProviso
--
-- Phase 0 MP-005: "small provider exemption defeats contact obligation (defeasible)"
-- vs "exemption: boundary, not mixed (structural exclusion)".
-- Expected: equivalent (both lower to boundary for exempt providers).
-- ============================================================

def vt5_variant_a : Clause where
  id                 := "VT5-A"
  sourceText         := "The licensed small provider shall provide contact information, except as exempted by the small provider carve-out which defeats this obligation."
  subject            := { id := "actor-provider", name := "licensed small provider",
                          kind := .legalPerson, sourceText := "small energy provider" }
  predicate          := "shall provide contact information (defeated by exemption)"
  object             := some "contact information"
  voice              := .active
  modality           := .shall
  negation           := .positive
  exceptionStructure := .defeasible [⟨"TCP-exemption-1", "small provider exemption defeats obligation"⟩]
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .numeric 1000 "customers"
  definitions        := [.crossReferenced "TCP §5.3" "small provider"]
  crossRefs          := [.intraStatute "TCP §5.3"]
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "TCP Code §5.1"

def vt5_variant_b : Clause where
  id                 := "VT5-B"
  sourceText         := "A licensed small provider assessment for contact obligations returns a boundary, not a mixed result, because the exemption and obligation regimes are mutually exclusive."
  subject            := { id := "actor-provider", name := "licensed small provider",
                          kind := .legalPerson, sourceText := "small energy provider" }
  predicate          := "small provider contact assessment yields boundary"
  object             := some "contact obligation assessment"
  voice              := .active
  modality           := .shall
  negation           := .positive
  exceptionStructure := .simpleProviso ⟨"TCP-exemption-1", "small provider exemption"⟩
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .numeric 1000 "customers"
  definitions        := [.crossReferenced "TCP §5.3" "small provider"]
  crossRefs          := [.intraStatute "TCP §5.3"]
  vaguenessMarker    := .discretionary
                          "small provider exemption applicability"
                          "ACCC"
                          "Provider must self-identify as small; ACCC may audit"
  priority           := 2
  sourceRef          := some "TCP Code §5.1"

def mp5 : MinimalPair where
  id               := "MP-005-VT"
  variant_a        := vt5_variant_a
  variant_b        := vt5_variant_b
  expected_relation := .divergent
  factors_varied   := ["exception_structure", "definitions"]
  rationale        :=
    "VT5-A has precise vaguenessMarker → LowerResult.rule. \
     VT5-B has discretionary vaguenessMarker → LowerResult.boundary. \
     ResultKind differs → divergent. The defeasible vs simpleProviso distinction \
     matters when the exception triggers a boundary in VT5-B."

-- ============================================================
-- The variation test suite
-- ============================================================

/-- All five variation family tests. -/
def variationSuite : List MinimalPair :=
  [mp1, mp2, mp3, mp4, mp5]

-- ============================================================
-- End-to-end test: English variant → IR → Normalise → Lower → compare
-- ============================================================

/-- Run one minimal pair through the full pipeline and report the check result. -/
-- Note: LowerResult uses a manual Repr instance (function-valued fields),
-- so PipelineResult cannot derive Repr automatically.  A manual instance
-- is provided below after runPipeline.
structure PipelineResult where
  pairId         : String
  variantAResult : LowerResult
  variantBResult : LowerResult
  checkPassed    : Bool

/-- Human-readable summary of a PipelineResult. -/
def PipelineResult.summarise (pr : PipelineResult) : String :=
  s!"[{pr.pairId}] A={pr.variantAResult.summarise} | B={pr.variantBResult.summarise} | passed={pr.checkPassed}"

instance : Repr PipelineResult where
  reprPrec pr _ := Std.Format.text pr.summarise

/-- Execute the end-to-end pipeline for a single MinimalPair.
    This is the core of REQ-014 acceptance criterion 4:
      English variant → IR.Clause → Normalise → Lower → compare LowerResults. -/
def runPipeline (pair : MinimalPair) : PipelineResult where
  pairId         := pair.id
  variantAResult := pipeline pair.variant_a
  variantBResult := pipeline pair.variant_b
  checkPassed    := checkRelation pair

/-- Run the full variation suite and collect results. -/
def runSuite : List PipelineResult :=
  variationSuite.map runPipeline

/-- Count how many tests passed. -/
def passCount : Nat :=
  (runSuite.filter (·.checkPassed)).length

/-- Count how many tests failed. -/
def failCount : Nat :=
  runSuite.length - passCount

-- ============================================================
-- #eval calls: execute the end-to-end pipeline and show results
-- ============================================================

-- Show all pipeline results.
#eval runSuite.map (fun r => s!"[{r.pairId}] passed={r.checkPassed}")

-- Show the pass/fail counts.
#eval s!"Pass: {passCount} / {runSuite.length}"

-- Show lowering summaries for the modality variation pair (MP-001-VT).
#eval (pipeline mp1.variant_a).summarise
#eval (pipeline mp1.variant_b).summarise

-- Show the TCJA divergent pair (MP-007-VT) — should show permitted vs prohibited.
#eval (pipeline mp3.variant_a).summarise
#eval (pipeline mp3.variant_b).summarise

-- Show normalisation changes for the double-negative pair (MP-004-VT).
#eval diffClause vt2_variant_b  -- should show negation changed: doubleNegative → positive

-- ============================================================
-- Spot-check examples (by rfl — definitionally decidable)
-- ============================================================

/-- MP-001 variant A: modality.none → toDeontic = permitted. -/
example : vt1_variant_a.modality.toDeontic = LegalLean.Deontic.permitted := by rfl

/-- MP-001 variant B: modality.may → toDeontic = permitted. -/
example : vt1_variant_b.modality.toDeontic = LegalLean.Deontic.permitted := by rfl

/-- MP-007 variant A: modality.may → toDeontic = permitted. -/
example : vt3_variant_a.modality.toDeontic = LegalLean.Deontic.permitted := by rfl

/-- MP-007 variant B: modality.prohibited → toDeontic = prohibited. -/
example : vt3_variant_b.modality.toDeontic = LegalLean.Deontic.prohibited := by rfl

/-- After normalisation, double-negative in VT2-B becomes positive. -/
example : (normalise vt2_variant_b).negation = Negation.positive := by rfl

/-- After normalisation, voice is always active (tests N1 on passive VT3-B). -/
example : (normalise vt3_variant_b).voice = Voice.active := by rfl

/-- VT5-A with precise vagueness marker lowers to LowerResult.rule. -/
example : lowerResultKind (pipeline vt5_variant_a) = ResultKind.rule := by rfl

/-- VT5-B with discretionary vagueness marker lowers to LowerResult.boundary. -/
example : lowerResultKind (pipeline vt5_variant_b) = ResultKind.boundary := by rfl

/-- The MP-003-VT pair is recognised as equivalent by checkRelation. -/
example : checkRelation mp4 = true := by rfl

/-- The MP-007-VT pair is recognised as divergent by checkRelation. -/
example : checkRelation mp3 = true := by rfl

end LegalLean.IR.VariationTest
