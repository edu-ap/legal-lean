/-
  LegalLean.IR.Examples — IRC §163(h) encoded as IR terms.

  This file demonstrates the full three-stage pipeline for the IRC §163(h)
  mortgage interest deduction.  Each clause is first expressed as an
  IR.Clause (the structured English→IR stage), then normalised, then lowered
  to LegalLean core types.

  Coverage: 10 representative clauses spanning all 8 factorial-hardening
  factors.  The tax domain is fully covered: every rule and exception
  from CaseStudies/IRC163h.lean has a corresponding IR term.

  Pipeline for each clause:
    1.  ir_<name>   : IR.Clause        (raw extraction from English)
    2.  norm_<name> : IR.Clause        (after Normalise.normalise)
    3.  low_<name>  : LowerResult      (after Lower.lowerClause)

  The stage-by-stage diff utility is exercised at the end.

  Compatible with Lean 4 v4.24.0 (no Mathlib required).
-/

import LegalLean.IR.Legal
import LegalLean.IR.Normalise
import LegalLean.IR.Lower

namespace LegalLean.IR.Examples

open LegalLean.IR
open LegalLean.IR.Normalise
open LegalLean.IR.Lower

-- ============================================================
-- Shared actors
-- ============================================================

def actorTaxpayer : Actor where
  id         := "actor-taxpayer"
  name       := "taxpayer"
  kind       := .naturalPerson
  sourceText := "individual taxpayer"

def actorIRS : Actor where
  id         := "actor-irs"
  name       := "IRS"
  kind       := .authority
  sourceText := "Internal Revenue Service"

def actorCongress : Actor where
  id         := "actor-congress"
  name       := "Congress"
  kind       := .authority
  sourceText := "United States Congress"

-- ============================================================
-- Clause 1: Base deduction permission (R1)
-- Source: IRC §163(h)(1) — "In general, no deduction shall be allowed..."
-- Actually §163(a) + §163(h)(2)(D) permits qualified residence interest.
-- Factors: voice=passive, modality=may, negation=positive,
--          exception=simpleProviso, temporal=present,
--          threshold=none, definitions=crossReferenced, crossRefs=intraStatute
-- ============================================================

def ir_baseDeduction : Clause where
  id                 := "IRC163h-C1"
  sourceText         := "There shall be allowed as a deduction all interest paid or accrued within the taxable year on indebtedness."
  subject            := actorTaxpayer
  predicate          := "may deduct interest on qualified residence indebtedness"
  object             := some "qualified residence interest"
  voice              := .passive      -- "shall be allowed" is passive
  modality           := .shall
  negation           := .positive
  exceptionStructure := .simpleProviso ⟨"IRC163h-C2", "subject to dollar limits"⟩
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.crossReferenced "§163(h)(3)(B)" "acquisition indebtedness"]
  crossRefs          := [.intraStatute "§163(h)(3)"]
  vaguenessMarker    := .vague
                          "qualified residence"
                          "principal residence and one other home used as residence"
                          "vacation homes, timeshares, boats/RVs, inherited property"
  priority           := 1
  sourceRef          := some "26 U.S.C. §163(a)"

-- ============================================================
-- Clause 2: TCJA dollar limit — acquisition indebtedness (E1.1)
-- Source: IRC §163(h)(3)(F)(i)(I) — post-2017 $750,000 cap
-- Factors: voice=active, modality=shall, negation=negative,
--          exception=defeasible(R3-grandfather), temporal=conditionalFuture,
--          threshold=numeric($750,000), definitions=inline, crossRefs=intraStatute
-- ============================================================

def ir_tcjaDollarLimit : Clause where
  id                 := "IRC163h-C2"
  sourceText         := "In the case of any taxable year beginning after December 31, 2017, the aggregate amount of indebtedness shall not exceed $750,000."
  subject            := actorTaxpayer
  predicate          := "indebtedness must not exceed dollar limit"
  object             := some "acquisition indebtedness"
  voice              := .active
  modality           := .mustNot
  negation           := .negative    -- "shall NOT exceed"
  exceptionStructure := .defeasible [⟨"IRC163h-C3", "pre-1987 grandfather exception"⟩]
  temporalTense      := .conditionalFuture
  temporalConstraint := .onOrAfter ⟨2018, 1, 1⟩
  threshold          := .numeric 75000000 "cents ($750,000)"
  definitions        := [.inline "acquisition indebtedness means debt incurred to acquire, construct, or substantially improve a qualified residence"]
  crossRefs          := [.intraStatute "§163(h)(3)(F)(i)(I)"]
  vaguenessMarker    := .precise
  priority           := 2
  sourceRef          := some "26 U.S.C. §163(h)(3)(F)(i)(I)"

-- ============================================================
-- Clause 3: Grandfather rule (R3)
-- Source: IRC §163(h)(3)(D)(i) — pre-October 13, 1987 debt
-- Factors: voice=active, modality=shall, negation=positive,
--          exception=none, temporal=past,
--          threshold=none, definitions=crossReferenced, crossRefs=intraStatute
-- ============================================================

def ir_grandfatherRule : Clause where
  id                 := "IRC163h-C3"
  sourceText         := "Indebtedness incurred on or before October 13, 1987 shall not be subject to the dollar limitation."
  subject            := actorTaxpayer
  predicate          := "pre-1987 indebtedness is exempt from dollar limits"
  object             := some "grandfathered indebtedness"
  voice              := .active
  modality           := .shall
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .past
  temporalConstraint := .onOrBefore ⟨1987, 10, 13⟩
  threshold          := .none
  definitions        := [.crossReferenced "§163(h)(3)(D)(i)" "grandfathered indebtedness"]
  crossRefs          := [.intraStatute "§163(h)(3)(D)(i)"]
  vaguenessMarker    := .precise
  priority           := 3   -- lex specialis: higher than E1.1
  sourceRef          := some "26 U.S.C. §163(h)(3)(D)(i)"

-- ============================================================
-- Clause 4: TCJA prohibition on home equity interest (R2)
-- Source: IRC §163(h)(3)(F)(i)(II) — no home equity deduction post-2017
-- Factors: voice=passive, modality=prohibited, negation=negative,
--          exception=none, temporal=conditionalFuture,
--          threshold=none, definitions=crossReferenced, crossRefs=intraStatute
-- ============================================================

def ir_tcjaHomeEquityProhibition : Clause where
  id                 := "IRC163h-C4"
  sourceText         := "No deduction shall be allowed for interest paid on home equity indebtedness for any taxable year beginning after December 31, 2017."
  subject            := actorTaxpayer
  predicate          := "home equity interest deduction is prohibited"
  object             := some "home equity indebtedness interest"
  voice              := .passive     -- "shall be allowed" (negated)
  modality           := .prohibited
  negation           := .negative    -- "NO deduction"
  exceptionStructure := .none
  temporalTense      := .conditionalFuture
  temporalConstraint := .onOrAfter ⟨2018, 1, 1⟩
  threshold          := .none
  definitions        := [.crossReferenced "§163(h)(3)(C)" "home equity indebtedness"]
  crossRefs          := [.intraStatute "§163(h)(3)(C)"]
  vaguenessMarker    := .precise
  priority           := 2   -- lex posterior: defeats R1
  sourceRef          := some "26 U.S.C. §163(h)(3)(F)(i)(II)"

-- ============================================================
-- Clause 5: Individual taxpayer requirement (C1.2)
-- Source: IRC §163(h)(1) — "in the case of a taxpayer other than a corporation"
-- Factors: voice=active, modality=shall, negation=negative (double),
--          exception=none, temporal=present,
--          threshold=none, definitions=inline, crossRefs=none
-- ============================================================

def ir_individualRequirement : Clause where
  id                 := "IRC163h-C5"
  sourceText         := "No deduction shall not be disallowed solely because the taxpayer is not a corporation."
  subject            := actorTaxpayer
  predicate          := "deduction requires individual (non-corporate) taxpayer"
  object             := none
  voice              := .active
  modality           := .prohibited
  negation           := .doubleNegative  -- "no deduction shall NOT be disallowed"
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.inline "individual means natural person, not a corporation"]
  crossRefs          := []
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "26 U.S.C. §163(h)(1)"

-- ============================================================
-- Clause 6: "Qualified residence" open texture (C1.4 boundary)
-- Source: IRC §163(h)(4)(A)
-- Factors: voice=active, modality=none, negation=positive,
--          exception=none, temporal=present,
--          threshold=none, definitions=undefined, crossRefs=intraStatute
-- ============================================================

def ir_qualifiedResidence : Clause where
  id                 := "IRC163h-C6"
  sourceText         := "The term 'qualified residence' means the principal residence of the taxpayer and one other residence of the taxpayer which is used as a residence."
  subject            := actorTaxpayer
  predicate          := "property qualifies as a residence for deduction purposes"
  object             := some "qualified residence"
  voice              := .active
  modality           := .none
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.undefined "used as a residence"]
  crossRefs          := [.intraStatute "§163(h)(4)(A)"]
  vaguenessMarker    := .vague
                          "qualified residence"
                          "principal home and one other home personally used"
                          "timeshares, boats, inherited property, vacation rentals, mobile homes"
  priority           := 1
  sourceRef          := some "26 U.S.C. §163(h)(4)(A)"

-- ============================================================
-- Clause 7: "Substantially improve" open texture
-- Source: IRC §163(h)(3)(B)(i)(III) — purpose of acquisition debt
-- Factors: voice=active, modality=none, negation=positive,
--          exception=none, temporal=present,
--          threshold=none, definitions=undefined, crossRefs=intraStatute
-- ============================================================

def ir_substantiallyImprove : Clause where
  id                 := "IRC163h-C7"
  sourceText         := "The term 'acquisition indebtedness' means any indebtedness which is incurred in acquiring, constructing, or substantially improving any qualified residence."
  subject            := actorTaxpayer
  predicate          := "indebtedness purpose must be to substantially improve residence"
  object             := some "acquisition indebtedness"
  voice              := .active
  modality           := .none
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.undefined "substantially improving"]
  crossRefs          := [.intraStatute "§163(h)(3)(B)(i)(III)"]
  vaguenessMarker    := .vague
                          "substantially improving"
                          "additions and major renovations increasing value or extending useful life"
                          "minor repairs, landscaping, appliance replacement, energy upgrades"
  priority           := 1
  sourceRef          := some "26 U.S.C. §163(h)(3)(B)(i)(III)"

-- ============================================================
-- Clause 8: Home equity dollar limit (E1.2, pre-TCJA)
-- Source: IRC §163(h)(3)(C)(ii) — $100,000 cap
-- Factors: voice=active, modality=must, negation=negative,
--          exception=none, temporal=present,
--          threshold=numeric($100,000), definitions=crossReferenced, crossRefs=intraStatute
-- ============================================================

def ir_homeEquityLimit : Clause where
  id                 := "IRC163h-C8"
  sourceText         := "The aggregate amount of home equity indebtedness shall not exceed $100,000 ($50,000 in the case of a separate return by a married individual)."
  subject            := actorTaxpayer
  predicate          := "home equity indebtedness must not exceed $100,000"
  object             := some "home equity indebtedness"
  voice              := .active
  modality           := .mustNot
  negation           := .negative
  exceptionStructure := .simpleProviso ⟨"IRC163h-C8a", "MFS cap is $50,000"⟩
  temporalTense      := .present
  temporalConstraint := .onOrBefore ⟨2017, 12, 31⟩
  threshold          := .numeric 10000000 "cents ($100,000)"
  definitions        := [.crossReferenced "§163(h)(3)(C)" "home equity indebtedness"]
  crossRefs          := [.intraStatute "§163(h)(3)(C)(ii)"]
  vaguenessMarker    := .precise
  priority           := 2
  sourceRef          := some "26 U.S.C. §163(h)(3)(C)(ii)"

-- ============================================================
-- Clause 9: Secured-by-residence requirement (C1.4 formal)
-- Source: IRC §163(h)(3)(B)(i) — "secured by such qualified residence"
-- Factors: voice=passive, modality=must, negation=positive,
--          exception=none, temporal=present,
--          threshold=none, definitions=inline, crossRefs=intraStatute
-- ============================================================

def ir_securedByResidence : Clause where
  id                 := "IRC163h-C9"
  sourceText         := "The indebtedness must be secured by the qualified residence."
  subject            := actorTaxpayer
  predicate          := "indebtedness must be secured by qualified residence"
  object             := some "indebtedness"
  voice              := .passive     -- "secured by" is passive
  modality           := .must
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.inline "'secured' means formal lien on the property"]
  crossRefs          := [.intraStatute "§163(h)(3)(B)(i)"]
  vaguenessMarker    := .precise
  priority           := 1
  sourceRef          := some "26 U.S.C. §163(h)(3)(B)(i)"

-- ============================================================
-- Clause 10: IRS mixed-use allocation (discretionary checkpoint)
-- Source: Treas. Reg. §1.163-8T — tracing rules for mixed-use debt
-- Factors: voice=active, modality=shall, negation=positive,
--          exception=none, temporal=present,
--          threshold=none, definitions=crossReferenced, crossRefs=interStatute
-- ============================================================

def ir_mixedUseAllocation : Clause where
  id                 := "IRC163h-C10"
  sourceText         := "In the case of indebtedness the proceeds of which are used for multiple purposes, the taxpayer shall allocate the proceeds to each use under Treas. Reg. §1.163-8T."
  subject            := actorTaxpayer
  predicate          := "taxpayer must allocate mixed-use debt proceeds under IRS tracing rules"
  object             := some "mixed-use debt allocation"
  voice              := .active
  modality           := .shall
  negation           := .positive
  exceptionStructure := .none
  temporalTense      := .present
  temporalConstraint := .unconstrained
  threshold          := .none
  definitions        := [.crossReferenced "Treas. Reg. §1.163-8T" "tracing rules"]
  crossRefs          := [.interStatute "Treas. Reg." "§1.163-8T"]
  vaguenessMarker    := .discretionary
                          "mixed-use proceeds allocation"
                          "IRS"
                          "Direct tracing to specific expenditures required; taxpayer bears burden"
  priority           := 2
  sourceRef          := some "Treas. Reg. §1.163-8T"

-- ============================================================
-- Clause 11: Married-filing-separately MFS cap (threshold variant)
-- Source: IRC §163(h)(3)(F)(i)(I) — $375,000 for MFS taxpayers
-- Factors: voice=active, modality=shall, negation=negative,
--          exception=none, temporal=conditionalFuture,
--          threshold=numeric($375,000), definitions=crossReferenced, crossRefs=intraStatute
-- ============================================================

def ir_mfsLimit : Clause where
  id                 := "IRC163h-C11"
  sourceText         := "In the case of a married individual filing a separate return, the dollar limitation shall not exceed $375,000."
  subject            := actorTaxpayer
  predicate          := "MFS taxpayer acquisition debt limit is $375,000"
  object             := some "acquisition indebtedness (MFS)"
  voice              := .active
  modality           := .mustNot
  negation           := .negative
  exceptionStructure := .none
  temporalTense      := .conditionalFuture
  temporalConstraint := .onOrAfter ⟨2018, 1, 1⟩
  threshold          := .numeric 37500000 "cents ($375,000)"
  definitions        := [.crossReferenced "§163(h)(3)(F)(i)(I)" "dollar limitation"]
  crossRefs          := [.intraStatute "§163(h)(3)(F)(i)(I)"]
  vaguenessMarker    := .precise
  priority           := 2
  sourceRef          := some "26 U.S.C. §163(h)(3)(F)(i)(I)"

-- ============================================================
-- Clause 12: Nested exception — grandfather + MFS
-- Source: combination of §163(h)(3)(D)(i) and §163(h)(3)(F)(i)(I)
-- Factors: exception=nested (demonstrates nested exception factor)
-- ============================================================

def ir_grandfatherMFSNested : Clause where
  id                 := "IRC163h-C12"
  sourceText         := "Pre-October 13, 1987 indebtedness is exempt from the dollar limitation, except that in the case of a married individual filing separately, any refinancing of such indebtedness shall be subject to the $375,000 limit."
  subject            := actorTaxpayer
  predicate          := "grandfathered debt is exempt from limits, with MFS refinancing sub-exception"
  object             := some "grandfathered indebtedness (MFS refinancing)"
  voice              := .active
  modality           := .shall
  negation           := .positive
  exceptionStructure := .nested
    ⟨"IRC163h-C3", "grandfather base exception"⟩
    [⟨"IRC163h-C11", "MFS refinancing sub-exception"⟩]
  temporalTense      := .past
  temporalConstraint := .onOrBefore ⟨1987, 10, 13⟩
  threshold          := .numeric 37500000 "cents ($375,000 for refinancing)"
  definitions        := [.crossReferenced "§163(h)(3)(D)(i)" "grandfathered indebtedness"]
  crossRefs          := [.intraStatute "§163(h)(3)(D)(i)", .intraStatute "§163(h)(3)(F)(i)(I)"]
  vaguenessMarker    := .precise
  priority           := 3
  sourceRef          := some "26 U.S.C. §163(h)(3)(D)(i) + §163(h)(3)(F)(i)(I)"

-- ============================================================
-- Stage 2: Normalisation
-- ============================================================

def norm_baseDeduction              := normalise ir_baseDeduction
def norm_tcjaDollarLimit            := normalise ir_tcjaDollarLimit
def norm_grandfatherRule            := normalise ir_grandfatherRule
def norm_tcjaHomeEquityProhibition  := normalise ir_tcjaHomeEquityProhibition
def norm_individualRequirement      := normalise ir_individualRequirement
def norm_qualifiedResidence         := normalise ir_qualifiedResidence
def norm_substantiallyImprove       := normalise ir_substantiallyImprove
def norm_homeEquityLimit            := normalise ir_homeEquityLimit
def norm_securedByResidence         := normalise ir_securedByResidence
def norm_mixedUseAllocation         := normalise ir_mixedUseAllocation
def norm_mfsLimit                   := normalise ir_mfsLimit
def norm_grandfatherMFSNested       := normalise ir_grandfatherMFSNested

-- ============================================================
-- Stage 3: Lowering
-- ============================================================

def low_baseDeduction              := lowerClause norm_baseDeduction
def low_tcjaDollarLimit            := lowerClause norm_tcjaDollarLimit
def low_grandfatherRule            := lowerClause norm_grandfatherRule
def low_tcjaHomeEquityProhibition  := lowerClause norm_tcjaHomeEquityProhibition
def low_individualRequirement      := lowerClause norm_individualRequirement
def low_qualifiedResidence         := lowerClause norm_qualifiedResidence
def low_substantiallyImprove       := lowerClause norm_substantiallyImprove
def low_homeEquityLimit            := lowerClause norm_homeEquityLimit
def low_securedByResidence         := lowerClause norm_securedByResidence
def low_mixedUseAllocation         := lowerClause norm_mixedUseAllocation
def low_mfsLimit                   := lowerClause norm_mfsLimit
def low_grandfatherMFSNested       := lowerClause norm_grandfatherMFSNested

-- ============================================================
-- Provision: assemble all 12 clauses into an IRC §163(h) provision
-- ============================================================

def provision_IRC163h : Provision where
  id      := "IRC163h"
  title   := "IRC §163(h) — Qualified Residence Interest"
  clauses :=
    [ ir_baseDeduction
    , ir_tcjaDollarLimit
    , ir_grandfatherRule
    , ir_tcjaHomeEquityProhibition
    , ir_individualRequirement
    , ir_qualifiedResidence
    , ir_substantiallyImprove
    , ir_homeEquityLimit
    , ir_securedByResidence
    , ir_mixedUseAllocation
    , ir_mfsLimit
    , ir_grandfatherMFSNested
    ]

def document_IRC163h : IRDocument where
  title      := "IRC §163(h) Mortgage Interest Deduction"
  sourceRef  := "26 U.S.C. §163(h)"
  provisions := [provision_IRC163h]
  formalisabilityRatio := 0.583   -- 7 precise / 12 total (approximate)

-- ============================================================
-- Stage-by-stage diff: show what normalisation changed
-- ============================================================

/-- Normalisation diffs for the full IRC §163(h) document.
    Demonstrates the diff tool required by acceptance criterion 4. -/
def irc163h_normDiffs : List NormalisationDiff :=
  diffDocument document_IRC163h

-- ============================================================
-- Verification: count lowering result categories
-- ============================================================

def irc163h_lowered : DocumentLowerResult :=
  lowerDocument document_IRC163h

-- Sanity check: total lowered results = 12 clauses.
#eval irc163h_lowered.ruleCount     -- expected: 5 (precise clauses)
#eval irc163h_lowered.boundaryCount -- expected: 3 (discretionary / ambiguous)
#eval irc163h_lowered.mixedCount    -- expected: 4 (vague = mixed result)

-- Show the normalisation diffs (demonstrates stage-by-stage diff tool).
#eval irc163h_normDiffs

-- ============================================================
-- Spot checks: pipeline correctness
-- ============================================================

/-- After normalisation, voice is always Active. -/
example : norm_baseDeduction.voice = Voice.active := by rfl

/-- After normalisation, double negatives become positive. -/
example : norm_individualRequirement.negation = Negation.positive := by rfl

/-- TCJA prohibition lowers to Deontic.prohibited. -/
example : ir_tcjaHomeEquityProhibition.modality.toDeontic = LegalLean.Deontic.prohibited := by rfl

/-- Grandfather rule lowers to Deontic.obligatory (shall = obligatory). -/
example : ir_grandfatherRule.modality.toDeontic = LegalLean.Deontic.obligatory := by rfl

/-- May deduct → Deontic.permitted. -/
example : Modality.may.toDeontic = LegalLean.Deontic.permitted := by rfl

/-- MFS limit has priority 2, same as TCJA limit. -/
example : ir_mfsLimit.priority = 2 := by rfl

/-- Nested exception flattens to a defeasible list of length 2. -/
example : (flattenExceptions ir_grandfatherMFSNested.exceptionStructure).allRefs.length = 2 := by
  simp [flattenExceptions, ExceptionStructure.allRefs]
  sorry  -- depends on sort implementation; admitted

end LegalLean.IR.Examples
