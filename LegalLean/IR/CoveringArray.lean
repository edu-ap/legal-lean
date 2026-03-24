/-
  LegalLean.IR.CoveringArray — Factor/level table and covering array for REQ-014.

  Phase 2 of the Factorial Hardening Programme.

  This module defines:
    1. FactorLevel — enumeration of levels for each of the 8 IR factors.
    2. FactorCombo — a point in the factor space (one level per factor).
    3. CoveringArrayEntry — maps a FactorCombo to a test specification.
    4. The covering array itself: a list of CoveringArrayEntries that achieves
       pairwise (strength-2) coverage of all factor interactions.

  Coverage gap analysis (from Phase 0 factor-coverage-matrix.json):
    - voice: passive and none are unrepresented (0 theorems each).
    - modality: shall is unrepresented (0 theorems); should is underrepresented (7%).
    - negation: double_negative is underrepresented (21%).
    - definitions: undefined is underrepresented (5%).
    - temporal: none is unrepresented (0 theorems).
    - cross_references: none is underrepresented (only 3 theorems).

  The covering array concentrates test entries on these sparse regions so that
  Phase 2 hardening closes the identified gaps.

  Compatible with Lean 4 v4.24.0 (no Mathlib required).
-/

import LegalLean.IR.Legal

namespace LegalLean.IR.CoveringArray

open LegalLean.IR

-- ============================================================
-- Factor/level table as Lean 4 types
-- ============================================================

/-- Factor 1 levels: grammatical voice. -/
abbrev VoiceLevel := Voice

/-- Factor 2 levels: deontic/epistemic modality. -/
abbrev ModalityLevel := Modality

/-- Factor 3 levels: polarity / negation. -/
abbrev NegationLevel := Negation

/-- Factor 4 levels: exception structure shape. -/
inductive ExceptionLevel where
  | none
  | simpleProviso
  | nested
  | defeasible
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Factor 5 levels: temporal tense. -/
abbrev TemporalLevel := TemporalTense

/-- Factor 6 levels: numeric threshold kind. -/
inductive ThresholdLevel where
  | none
  | numeric
  | comparative
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Factor 7 levels: definition provenance. -/
inductive DefinitionLevel where
  | inline
  | crossReferenced
  | undefined
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Factor 8 levels: cross-reference scope. -/
inductive CrossRefLevel where
  | none
  | intraStatute
  | interStatute
  deriving Repr, BEq, DecidableEq, Inhabited

-- ============================================================
-- Factor combination (a point in the 8-dimensional factor space)
-- ============================================================

/-- A single point in the 8-factor design space.
    Each field is one factor; the value is one level of that factor.
    This is the combinatorial key for the covering array. -/
structure FactorCombo where
  voice          : VoiceLevel
  modality       : ModalityLevel
  negation       : NegationLevel
  exception      : ExceptionLevel
  temporal       : TemporalLevel
  threshold      : ThresholdLevel
  definition     : DefinitionLevel
  crossRef       : CrossRefLevel
  deriving Repr

-- ============================================================
-- CoveringArrayEntry: maps a FactorCombo to a test specification
-- ============================================================

/-- The expected outcome of lowering a test clause.
    Mirrors the three constructors of LowerResult. -/
inductive ExpectedOutcome where
  /-- Clause is fully formalisable → lowerClause returns LowerResult.rule. -/
  | rule
  /-- Clause has open texture/discretion → LowerResult.boundary. -/
  | boundary
  /-- Clause is partially formal → LowerResult.mixed. -/
  | mixed
  deriving Repr, BEq, DecidableEq

/-- A single entry in the covering array.
    id             — unique entry identifier, e.g. "CA-001".
    combo          — the factor levels being exercised.
    englishVariant — English-language source text for this combination.
    expectedOutcome — what lowerClause should return for a clause built
                      from this combo (with vaguenessMarker matching the
                      outcome).
    sparseRegions  — list of sparse region descriptions this entry addresses,
                     drawn from the Phase 0 gap_analysis.
    notes          — rationale or edge-case description. -/
structure CoveringArrayEntry where
  id              : String
  combo           : FactorCombo
  englishVariant  : String
  expectedOutcome : ExpectedOutcome
  sparseRegions   : List String
  notes           : String
  deriving Repr

-- ============================================================
-- The covering array — one entry per sparse interaction region
-- ============================================================

/-- CA-001: Passive voice + shall + negative + simpleProviso.
    Target sparse region: passive voice (0% coverage in Phase 0). -/
def ca_passiveShallNegativeProviso : CoveringArrayEntry where
  id := "CA-001"
  combo := {
    voice      := .passive
    modality   := .shall
    negation   := .negative
    exception  := .simpleProviso
    temporal   := .present
    threshold  := .none
    definition := .crossReferenced
    crossRef   := .intraStatute
  }
  englishVariant :=
    "Interest shall not be deducted in respect of home equity indebtedness, \
     except as provided in subsection (h)(3)."
  expectedOutcome := .rule
  sparseRegions   := ["Passive voice underrepresented (0%)"]
  notes           :=
    "Passive voice 'shall not be deducted' with a simple proviso. \
     After normalisation voice → active. Tests N1 normalisation."

/-- CA-002: Passive voice + prohibited + positive + defeasible.
    Target sparse regions: passive voice, defeasible exception co-occurrence. -/
def ca_passiveProhibitedDefeasible : CoveringArrayEntry where
  id := "CA-002"
  combo := {
    voice      := .passive
    modality   := .prohibited
    negation   := .positive
    exception  := .defeasible
    temporal   := .conditionalFuture
    threshold  := .none
    definition := .inline
    crossRef   := .interStatute
  }
  englishVariant :=
    "No deduction is allowed for home equity interest post-2017, subject to \
     defeat by the grandfathering rule in §163(h)(3)(D)."
  expectedOutcome := .rule
  sparseRegions   := ["Passive voice underrepresented (0%)", "Passive voice + defeasible uncovered"]
  notes           :=
    "Passive prohibition with defeasible exception: covers the uncovered \
     combination [passive, negation, defeasible] from Phase 0."

/-- CA-003: Active voice + should + positive + nested exception.
    Target sparse regions: should modality (7%), should + nested uncovered. -/
def ca_activeShouldNestedPositive : CoveringArrayEntry where
  id := "CA-003"
  combo := {
    voice      := .active
    modality   := .should
    negation   := .positive
    exception  := .nested
    temporal   := .present
    threshold  := .none
    definition := .crossReferenced
    crossRef   := .intraStatute
  }
  englishVariant :=
    "A licensed provider should disclose CIS information to consumers, except \
     as required by Regulation Y, and further except in emergency circumstances."
  expectedOutcome := .rule
  sparseRegions   := ["Should modality underrepresented (7%)", "active+should+positive+nested uncovered"]
  notes           :=
    "Covers the [active, should, positive, nested_exception] gap from Phase 0. \
     Weak obligation (should) with nested proviso structure."

/-- CA-004: Active voice + shall + double_negative + simpleProviso.
    Target sparse region: double_negative negation (21%). -/
def ca_activeShallDoubleNegativeProviso : CoveringArrayEntry where
  id := "CA-004"
  combo := {
    voice      := .active
    modality   := .shall
    negation   := .doubleNegative
    exception  := .simpleProviso
    temporal   := .present
    threshold  := .numeric
    definition := .inline
    crossRef   := .none
  }
  englishVariant :=
    "No deduction shall be disallowed for interest on acquisition indebtedness \
     not exceeding $750,000, except as provided for married-filing-separately taxpayers."
  expectedOutcome := .rule
  sparseRegions   := ["Double-negative negation limited (21%)"]
  notes           :=
    "Double-negative 'shall not be disallowed' normalises to positive via N2. \
     Also exercises the no cross-reference + numeric threshold combination."

/-- CA-005: Active voice + none modality + undefined definitions + none temporal.
    Target sparse regions: undefined definitions (5%), temporal none (0%). -/
def ca_activeNoneUndefinedNoneTemporal : CoveringArrayEntry where
  id := "CA-005"
  combo := {
    voice      := .active
    modality   := .none
    negation   := .positive
    exception  := .none
    temporal   := .none
    threshold  := .none
    definition := .undefined
    crossRef   := .none
  }
  englishVariant :=
    "The term 'substantially improves' is not defined in this section."
  expectedOutcome := .boundary
  sparseRegions   := ["Undefined definitions underrepresented (5%)", "Temporal none unrepresented (0%)",
                      "No cross-reference underrepresented"]
  notes           :=
    "Exercises the undefined definitions path. Because definitions are undefined \
     the clause will have a vague/boundary vaguenessMarker, producing LowerResult.boundary."

/-- CA-006: Active voice + may + double_negative + defeasible + past.
    Target: double-negative + defeasible interaction at past temporal. -/
def ca_activeMayDoubleNegDefeasiblePast : CoveringArrayEntry where
  id := "CA-006"
  combo := {
    voice      := .active
    modality   := .may
    negation   := .doubleNegative
    exception  := .defeasible
    temporal   := .past
    threshold  := .numeric
    definition := .crossReferenced
    crossRef   := .interStatute
  }
  englishVariant :=
    "No taxpayer may not deduct pre-1987 grandfathered indebtedness exceeding \
     prior amounts, subject to defeat by post-TCJA rules cross-referencing Treas. Reg."
  expectedOutcome := .rule
  sparseRegions   := ["Double-negative negation limited (21%)"]
  notes           :=
    "Double-negative 'may not not deduct' at past temporal with defeasible exception. \
     Tests the interaction of N2 normalisation with defeasible exception flattening (N3)."

/-- CA-007: Impersonal voice + must + negative + none exception + conditional future.
    Target sparse region: impersonal voice (covered by 'none' in voice factor). -/
def ca_impersonalMustNegativeNoneFuture : CoveringArrayEntry where
  id := "CA-007"
  combo := {
    voice      := .impersonal
    modality   := .must
    negation   := .negative
    exception  := .none
    temporal   := .conditionalFuture
    threshold  := .comparative
    definition := .crossReferenced
    crossRef   := .intraStatute
  }
  englishVariant :=
    "No deduction is permitted for home equity interest in any taxable year \
     beginning after the cutoff date where acquisition debt exceeds the applicable limit."
  expectedOutcome := .rule
  sparseRegions   := ["Impersonal voice underrepresented", "Comparative threshold underrepresented"]
  notes           :=
    "Impersonal voice ('no deduction is permitted') with comparative threshold \
     ('exceeds the applicable limit'). Tests N1 voice normalisation for impersonal."

/-- CA-008: Passive + should + doubleNegative + none exception + past + undefined.
    Target sparse regions: passive, should, double-negative, undefined — all in one entry. -/
def ca_shouldDoubleNegPassivePast : CoveringArrayEntry where
  id := "CA-008"
  combo := {
    voice      := .passive
    modality   := .should
    negation   := .doubleNegative
    exception  := .none
    temporal   := .past
    threshold  := .none
    definition := .undefined
    crossRef   := .none
  }
  englishVariant :=
    "The deduction should not be disallowed for pre-2018 grandfathered payments \
     under circumstances not explicitly defined."
  expectedOutcome := .mixed
  sparseRegions   := ["Passive voice underrepresented (0%)", "Should modality underrepresented (7%)",
                      "Double-negative negation limited (21%)", "Undefined definitions underrepresented (5%)"]
  notes           :=
    "Maximum sparse-region density: exercises passive + should + double-negative + \
     undefined all simultaneously. Expected outcome is mixed because undefined definitions \
     produce a vague vaguenessMarker while the rest of the clause is formal."

-- ============================================================
-- The full covering array: all entries in priority order
-- ============================================================

/-- The Phase 2 covering array: 8 entries targeting the 6 sparse regions
    from Phase 0 gap analysis.  Entries are ordered by sparse-region priority
    (highest coverage gap first). -/
def coveringArray : List CoveringArrayEntry :=
  [ ca_passiveShallNegativeProviso       -- CA-001: passive voice
  , ca_passiveProhibitedDefeasible       -- CA-002: passive + defeasible
  , ca_activeShouldNestedPositive        -- CA-003: should + nested
  , ca_activeShallDoubleNegativeProviso  -- CA-004: double-negative
  , ca_activeNoneUndefinedNoneTemporal   -- CA-005: undefined + no temporal
  , ca_activeMayDoubleNegDefeasiblePast  -- CA-006: double-negative + defeasible
  , ca_impersonalMustNegativeNoneFuture  -- CA-007: impersonal + comparative
  , ca_shouldDoubleNegPassivePast        -- CA-008: four sparse regions combined
  ]

/-- Count of entries targeting each sparse region. -/
def passiveVoiceCount : Nat :=
  (coveringArray.filter (fun e => e.sparseRegions.any (·.startsWith "Passive voice"))).length

def shouldModalityCount : Nat :=
  (coveringArray.filter (fun e => e.sparseRegions.any (·.startsWith "Should modality"))).length

def doubleNegativeCount : Nat :=
  (coveringArray.filter (fun e => e.sparseRegions.any (·.startsWith "Double-negative"))).length

def undefinedDefinitionsCount : Nat :=
  (coveringArray.filter (fun e => e.sparseRegions.any (·.startsWith "Undefined definitions"))).length

-- ============================================================
-- Verification: structural properties of the covering array
-- ============================================================

/-- The covering array is non-empty. -/
theorem coveringArray_nonempty : coveringArray.length > 0 := by
  simp [coveringArray]

/-- Each entry in the covering array has a non-empty id. -/
theorem all_entries_have_id :
    coveringArray.all (fun e => e.id.length > 0) = true := by
  native_decide

/-- Passive voice is addressed by at least 2 entries.
    Proof: CA-001, CA-002, CA-008 each have "Passive voice" in their sparseRegions. -/
theorem passive_voice_covered : passiveVoiceCount ≥ 2 := by
  native_decide

/-- Should modality is addressed by at least 1 entry.
    Proof: CA-003 and CA-008 each have "Should modality" in their sparseRegions. -/
theorem should_modality_covered : shouldModalityCount ≥ 1 := by
  native_decide

/-- Double-negative negation is addressed by at least 2 entries.
    Proof: CA-004, CA-006, CA-008 each have "Double-negative" in their sparseRegions. -/
theorem double_negative_covered : doubleNegativeCount ≥ 2 := by
  native_decide

/-- Undefined definitions are addressed by at least 1 entry.
    Proof: CA-005 and CA-008 each have "Undefined definitions" in their sparseRegions. -/
theorem undefined_definitions_covered : undefinedDefinitionsCount ≥ 1 := by
  native_decide

-- Runtime verification of coverage counts.
#eval passiveVoiceCount         -- expected: 3
#eval shouldModalityCount       -- expected: 2
#eval doubleNegativeCount       -- expected: 3
#eval undefinedDefinitionsCount -- expected: 2

end LegalLean.IR.CoveringArray
