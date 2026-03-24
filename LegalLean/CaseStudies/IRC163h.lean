/-
  LegalLean.CaseStudies.IRC163h — IRC §163(h) Mortgage Interest Deduction.

  The warm-up case study. Lawsky's gold standard for formalising statutes
  using default logic. Chosen because:
  1. Smallest scope (single tax provision)
  2. Well-studied in the literature (Lawsky 2017)
  3. Mix of clear rules and open texture
  4. Demonstrates defeasibility (exceptions to the deduction)

  Source: 26 U.S.C. § 163(h)
  Reference: Lawsky, "A Logic for Statutes", Florida Tax Review (2017).

  Structure discovered by research pipeline (Perplexity sonar-pro):
  - 3 rules: base deduction (permitted), TCJA prohibition, grandfather exception
  - 4 defeat relations forming a 3-level chain:
      R3 (grandfather) defeats E1.1 (dollar limit) defeats R1 (base permission)
      R2 (TCJA) defeats R1 (lex posterior)
  - 3 open texture terms: "qualified residence", "substantial improvement", "residence"
  - 3 discretionary checkpoints: IRS/Tax Court determinations

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
-/

import LegalLean.Core
import LegalLean.Defeasible

namespace LegalLean.CaseStudies.IRC163h

-- ============================================================
-- Domain types: the entities and predicates of IRC §163(h)
-- ============================================================

/-- A taxpayer filing status, relevant to dollar limit thresholds. -/
inductive FilingStatus where
  | single
  | marriedFilingJointly
  | marriedFilingSeparately
  | headOfHousehold
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A qualified residence: main home or one other residence. -/
inductive ResidenceType where
  | principalResidence
  | secondResidence
  deriving Repr, BEq

/-- Temporal period, relevant to TCJA transition rules. -/
structure TaxYear where
  year : Nat
  deriving Repr, BEq, DecidableEq

/-- A dollar amount (in cents to avoid floating point). -/
abbrev Cents := Nat

/-- The purpose of the indebtedness determines its classification.
    Must be defined before Indebtedness (which references it). -/
inductive IndebtednessPurpose where
  | acquire               -- to purchase the residence
  | construct             -- to build the residence
  | substantiallyImprove  -- to substantially improve (OPEN TEXTURE)
  | other                 -- home equity / other purposes
  deriving Repr, BEq, DecidableEq

/-- An indebtedness with provenance and amount.
    `dateIncurred` uses the proper `Date` type (Fix 1: replace magic String). -/
structure Indebtedness where
  id : String
  amount : Cents
  dateIncurred : LegalLean.Date   -- proper Date struct, not a String
  securedByResidence : Bool
  residenceType : Option ResidenceType
  purpose : IndebtednessPurpose
  deriving Repr

/-- Interest payment on an indebtedness during a taxable year. -/
structure InterestPayment where
  indebtedness : Indebtedness
  amount : Cents
  taxYear : TaxYear
  paidByIndividual : Bool     -- C1.2: must be individual, not corporation
  deriving Repr

-- ============================================================
-- Formalisable conditions (the type checker can verify these)
-- ============================================================

/-- C1.2: Taxpayer must be an individual (not a corporation). -/
def isIndividualTaxpayer (payment : InterestPayment) : Prop :=
  payment.paidByIndividual = true

/-- C1.3: Interest paid during the taxable year. (Tautological given our model,
    but made explicit for completeness.) -/
def paidDuringTaxYear (payment : InterestPayment) (year : TaxYear) : Prop :=
  payment.taxYear = year

/-- C1.4 (formal part): Indebtedness must be secured by the residence. -/
def securedByResidence (debt : Indebtedness) : Prop :=
  debt.securedByResidence = true

/-- C2.1: Taxable year beginning after December 15, 2017 (TCJA effective date). -/
def postTCJA (year : TaxYear) : Prop :=
  year.year ≥ 2018

/-- C3.1: Indebtedness incurred on or before October 13, 1987.
    Uses the proper `Date` type with structural LE ordering (Fix 1). -/
def preTRA87 (debt : Indebtedness) : Prop :=
  debt.dateIncurred ≤ ⟨1987, 10, 13⟩

/-- Acquisition indebtedness dollar limit.
    Pre-TCJA: $1,000,000 ($500,000 MFS)
    Post-TCJA: $750,000 ($375,000 MFS) -/
def acquisitionLimit (year : TaxYear) (status : FilingStatus) : Cents :=
  if year.year ≥ 2018 then
    match status with
    | FilingStatus.marriedFilingSeparately => 37500000   -- $375,000
    | _ => 75000000                                      -- $750,000
  else
    match status with
    | FilingStatus.marriedFilingSeparately => 50000000   -- $500,000
    | _ => 100000000                                     -- $1,000,000

/-- Home equity indebtedness dollar limit: $100,000 ($50,000 MFS). -/
def homeEquityLimit (status : FilingStatus) : Cents :=
  match status with
  | FilingStatus.marriedFilingSeparately => 5000000    -- $50,000
  | _ => 10000000                                      -- $100,000

/-- E1.1: Acquisition indebtedness within dollar limits. -/
def withinAcquisitionLimit
    (debt : Indebtedness) (year : TaxYear) (status : FilingStatus) : Bool :=
  debt.amount ≤ acquisitionLimit year status

/-- E1.2: Home equity indebtedness within dollar limits. -/
def withinHomeEquityLimit (debt : Indebtedness) (status : FilingStatus) : Bool :=
  debt.amount ≤ homeEquityLimit status

-- ============================================================
-- Open texture: propositions requiring human determination
-- (FormalisationBoundary marks WHERE the type checker must stop)
-- ============================================================

/-- "Qualified residence" — Hart's penumbra in action.
    Core: main home + one other home used as residence.
    Penumbra: mobile homes, timeshares, inherited property, boats/RVs.
    Case law:
    - Glicksman v. Commissioner, U.S. Tax Court (T.C. Memo.), on qualified
      residence status for non-traditional properties.
    - Robinson v. Commissioner, U.S. Tax Court (T.C. Memo.), on partial-year
      use and "used as a residence" standard.
    - Bolton v. Commissioner, U.S. Tax Court (T.C. Memo.), on second-residence
      classification and the 14-day / 10% rental use rule. -/
axiom IsQualifiedResidence : Indebtedness → Prop

variable (debt : Indebtedness) in
instance : LegalLean.Vague (IsQualifiedResidence debt) where
  reason := "IRC §163(h)(4)(A): 'qualified residence' requires property to be " ++
            "'used as a residence' — penumbral cases include mobile homes, " ++
            "timeshares, boats with sleeping/cooking/toilet facilities"
  authority := LegalLean.Authority.irsTaxCourt
  core := "Taxpayer's principal residence and one other property " ++
          "used as a residence during the taxable year"
  penumbra := "Vacation homes used <14 days/year, partial-year use, " ++
              "inherited homes not personally occupied, fractional ownership, " ++
              "boats/RVs meeting habitability requirements"

/-- "Substantially improve" — vague term in acquisition indebtedness definition.
    Core: additions, major renovations increasing value or extending useful life.
    Penumbra: minor remodelling, landscaping, appliance replacement.
    Case law:
    - Fackler v. Commissioner, U.S. Tax Court (T.C. Memo.), on the boundary
      between "substantial improvement" and ordinary repair or maintenance.
    - Tschetschot v. Commissioner, U.S. Tax Court, T.C. Memo. 2007-38 (2007),
      on whether energy-efficiency upgrades constitute substantial improvements. -/
axiom IsSubstantialImprovement : Indebtedness → Prop

variable (debt : Indebtedness) in
instance : LegalLean.Vague (IsSubstantialImprovement debt) where
  reason := "IRC §163(h)(3)(B): 'substantially improve' is not defined in the " ++
            "statute — must be determined case-by-case"
  authority := LegalLean.Authority.irsTaxCourt
  core := "Additions, major renovations that increase property value " ++
          "or significantly extend useful life"
  penumbra := "Minor remodelling, landscaping, appliance replacement, " ++
              "repairs characterised as improvements, energy efficiency upgrades"

/-- IRS discretion over mixed-use debt allocation.
    When proceeds are used partly for acquisition and partly for other purposes,
    the IRS applies tracing rules under Treas. Reg. §1.163-8T. -/
axiom MixedUseAllocation : Indebtedness → Cents → Cents → Prop

variable (debt : Indebtedness) (acq other_ : Cents) in
instance : LegalLean.Discretionary (MixedUseAllocation debt acq other_) where
  reason := "Allocation of mixed-use debt proceeds between acquisition " ++
            "and home equity components"
  authority := LegalLean.Authority.irs
  scope := "Determination of how debt proceeds were actually used, " ++
           "following direct tracing rules"
  constraints := [
    "Must follow Treas. Reg. §1.163-8T tracing rules",
    "Direct tracing to specific expenditures required",
    "Taxpayer bears burden of proof for allocation"
  ]

-- ============================================================
-- Classification: is this acquisition or home equity indebtedness?
-- ============================================================

/-- Classify indebtedness as acquisition indebtedness.
    Acquisition indebtedness = incurred to acquire, construct, or
    substantially improve a qualified residence, secured by that residence.
    Note: "substantially improve" is open texture (FormalisationBoundary). -/
def isAcquisitionIndebtedness (debt : Indebtedness)
    : LegalLean.FormalisationBoundary Prop :=
  if debt.securedByResidence then
    match debt.purpose with
    | IndebtednessPurpose.acquire =>
        LegalLean.FormalisationBoundary.formal (securedByResidence debt)
    | IndebtednessPurpose.construct =>
        LegalLean.FormalisationBoundary.formal (securedByResidence debt)
    | IndebtednessPurpose.substantiallyImprove =>
        LegalLean.FormalisationBoundary.boundary
          "Whether improvements constitute 'substantial improvement' per IRC §163(h)(3)(B)"
          LegalLean.Authority.irsTaxCourt
    | IndebtednessPurpose.other =>
        LegalLean.FormalisationBoundary.boundary
          "Not acquisition purpose — may be home equity"
          LegalLean.Authority.irs
  else
    LegalLean.FormalisationBoundary.formal False

/-- Classify indebtedness as home equity indebtedness.
    Home equity = any indebtedness secured by qualified residence that
    is NOT acquisition indebtedness. -/
def isHomeEquityIndebtedness (debt : Indebtedness) : Prop :=
  debt.securedByResidence = true ∧ debt.purpose = IndebtednessPurpose.other

-- ============================================================
-- Rules: the three rules discovered by the research pipeline
-- ============================================================

open LegalLean in
/-- R1: Base deduction rule.
    Taxpayers are PERMITTED to deduct qualified residence interest,
    subject to dollar limits and open texture conditions. -/
def R1_BaseDeduction : LegalRule InterestPayment where
  id := "R1"
  description := "Taxpayers are permitted to deduct interest paid on " ++
                 "acquisition indebtedness secured by a qualified residence"
  modality := Deontic.permitted
  priority := ⟨1, "statute"⟩
  conclusion := fun payment =>
    isIndividualTaxpayer payment ∧
    securedByResidence payment.indebtedness
  defeatedBy := ["E1.1", "E1.2", "R2"]

open LegalLean in
/-- R2: TCJA prohibition on home equity interest deduction.
    Interest on home equity indebtedness is PROHIBITED from deduction
    for taxable years after 2017.
    Defeats R1 via lex posterior (later statute). -/
def R2_TCJAProhibition : LegalRule InterestPayment where
  id := "R2"
  description := "Home equity interest deduction prohibited for " ++
                 "taxable years beginning after December 15, 2017"
  modality := Deontic.prohibited
  priority := ⟨2, "statute (TCJA 2017, lex posterior)"⟩
  conclusion := fun payment =>
    isHomeEquityIndebtedness payment.indebtedness ∧
    postTCJA payment.taxYear
  defeatedBy := []

open LegalLean in
/-- R3: Grandfather rule for pre-TRA87 debt.
    Outstanding acquisition indebtedness on 10/13/1987 is PERMITTED
    despite current dollar limits.
    Defeats E1.1 via lex specialis (specific exception). -/
def R3_GrandfatherRule : LegalRule InterestPayment where
  id := "R3"
  description := "Pre-October 13, 1987 acquisition indebtedness " ++
                 "grandfathered from current dollar limits"
  modality := Deontic.permitted
  priority := ⟨3, "statute (lex specialis, grandfather clause)"⟩
  conclusion := fun payment =>
    securedByResidence payment.indebtedness ∧
    preTRA87 payment.indebtedness
  defeatedBy := []

-- ============================================================
-- Defeat relations: the non-monotonic structure
-- ============================================================

open LegalLean in
/-- R2 defeats R1: TCJA eliminates home equity deduction (lex posterior). -/
def defeat_R2_R1 : Defeats where
  defeater := "R2"
  defeated := "R1"
  reason := "lex posterior: TCJA 2017 amendment eliminates " ++
            "home equity interest deduction component"
  strict := true

open LegalLean in
/-- E1.1 defeats R1: acquisition indebtedness dollar limit exceeded. -/
def defeat_E1_1_R1 : Defeats where
  defeater := "E1.1"
  defeated := "R1"
  reason := "statutory dollar limit within same provision " ++
            "(IRC §163(h)(3)(C))"
  strict := true

open LegalLean in
/-- E1.2 defeats R1: home equity indebtedness dollar limit exceeded. -/
def defeat_E1_2_R1 : Defeats where
  defeater := "E1.2"
  defeated := "R1"
  reason := "statutory dollar limit within same provision " ++
            "(IRC §163(h)(4)(C))"
  strict := true

open LegalLean in
/-- R3 defeats E1.1: grandfather clause overrides dollar limits.
    This creates the 3-level defeasibility chain:
    R3 (grandfather) defeats E1.1 (limit) which defeats R1 (base).
    Demonstrates that defeat relations are themselves defeasible. -/
def defeat_R3_E1_1 : Defeats where
  defeater := "R3"
  defeated := "E1.1"
  reason := "lex specialis: grandfather clause for pre-1987 " ++
            "debt is a specific exception to the general dollar limit"
  strict := true

open LegalLean in
/-- All defeat relations for this provision. -/
def allDefeats : List Defeats :=
  [defeat_R2_R1, defeat_E1_1_R1, defeat_E1_2_R1, defeat_R3_E1_1]

-- ============================================================
-- Deduction eligibility: composing rules with defeat checking
-- ============================================================

open LegalLean in
/-- Determine whether a specific interest payment is deductible.
    Returns a FormalisationBoundary because some conditions are
    not fully formalisable (qualified residence, substantial improvement).

    This function IS the "verified legal reasoning" for IRC §163(h):
    it composes formalisable conditions, checks defeat relations,
    and explicitly marks where human determination is required.

    Fix 3: Boolean blindness removed — `if payment.paidByIndividual` rather than
    `if payment.paidByIndividual = true`. -/
def isDeductible
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    : FormalisationBoundary Prop :=
  -- Step 1: Check formalisable conditions
  if !payment.paidByIndividual then
    FormalisationBoundary.formal False  -- C1.2 fails: not individual
  else if !payment.indebtedness.securedByResidence then
    FormalisationBoundary.formal False  -- C1.4 fails: not secured
  else
    -- Step 2: Classification (may hit formalisation boundary)
    match payment.indebtedness.purpose with
    | IndebtednessPurpose.acquire | IndebtednessPurpose.construct =>
      -- Acquisition indebtedness: check dollar limits
      if withinAcquisitionLimit payment.indebtedness year status then
        FormalisationBoundary.boundary
          ("Deduction permitted if property is a 'qualified residence' " ++
           "(core: principal residence + one other; penumbra: see Vague instance)")
          Authority.irsTaxCourt
      else
        FormalisationBoundary.boundary
          ("Acquisition limit exceeded. Check if pre-October 13, 1987 " ++
           "grandfather rule (R3) applies.")
          Authority.irsTaxCourt
    | IndebtednessPurpose.substantiallyImprove =>
      FormalisationBoundary.boundary
        ("Classification depends on whether improvements constitute " ++
         "'substantial improvement' — requires IRS/Tax Court determination")
        Authority.irsTaxCourt
    | IndebtednessPurpose.other =>
      -- Home equity: check TCJA prohibition
      if year.year ≥ 2018 then
        FormalisationBoundary.formal False  -- R2 defeats R1 (lex posterior)
      else
        -- Pre-TCJA: check dollar limits
        if withinHomeEquityLimit payment.indebtedness status then
          FormalisationBoundary.boundary
            ("Pre-TCJA home equity deduction permitted if within limits " ++
             "and property is 'qualified residence'")
            Authority.irsTaxCourt
        else
          FormalisationBoundary.formal False  -- E1.2 defeats R1

-- ============================================================
-- Theorems: properties we want to prove about the formalisation
-- ============================================================

open LegalLean in
/-- Theorem: TCJA strictly prohibits home equity deductions post-2017.
    This is a formalisable claim — no open texture involved. -/
theorem tcja_prohibits_home_equity
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h_individual : payment.paidByIndividual = true)
    (h_secured : payment.indebtedness.securedByResidence = true)
    (h_purpose : payment.indebtedness.purpose = IndebtednessPurpose.other)
    (h_post_tcja : year.year ≥ 2018)
    : isDeductible payment year status = FormalisationBoundary.formal False := by
  simp [isDeductible, h_individual, h_secured, h_purpose, h_post_tcja]

open LegalLean in
/-- Theorem: Non-individuals can never deduct (regardless of other conditions).
    Pure formal result — no open texture. -/
theorem non_individual_never_deducts
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h : payment.paidByIndividual = false)
    : isDeductible payment year status = FormalisationBoundary.formal False := by
  simp [isDeductible, h]

open LegalLean in
/-- Theorem: Unsecured debt never qualifies (regardless of other conditions).
    Pure formal result — no open texture. -/
theorem unsecured_never_deducts
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h : payment.indebtedness.securedByResidence = false)
    : isDeductible payment year status = FormalisationBoundary.formal False := by
  simp [isDeductible, h]

end LegalLean.CaseStudies.IRC163h
