=== CODEX ADVERSARIAL REVIEW ===
Started: Mon Mar 16 19:52:52 UTC 2026
---

OpenAI Codex v0.101.0 (research preview)
--------
workdir: [redacted]
model: gpt-5.2-codex
provider: openai
approval: never
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: auto
session id: 019cf835-5d1a-7ce2-8d86-db82e3b6ea02
--------
user
You are an expert reviewer for JURIX (International Conference on Legal Knowledge and Information Systems) and an expert in both formal methods (Lean 4, dependent types, Curry-Howard correspondence) and AI & law (defeasible reasoning, legal knowledge representation, Hart's open texture).

You have been asked to provide the HARSHEST POSSIBLE academic criticism of a paper submission. Your job is to find weaknesses, not to praise. Be specific, cite evidence from the code, and propose concrete improvements.

## The Paper

The paper below presents "LegalLean", a framework for verified legal reasoning built on Lean 4 dependent types. It claims to encode Hart's "open texture" as a first-class type (FormalisationBoundary) and proves 28 theorems with zero sorry stubs across 3 case studies.

## Questions You Must Answer

1. **Which theorems are trivial (just unfolding definitions) and which prove genuine properties about legal reasoning?** For each of the 28 theorems, classify as: trivial (unit-test level), moderate (structural property), or substantive (genuinely advances understanding). Be specific.

2. **Is FormalisationBoundary a genuine contribution or just a labelled union type?** Could the same thing be achieved with a simple `data Result = Formal a | NeedsHuman String` in Haskell? What does the Lean 4 type system add that a simpler system could not? Is the RequiresHumanDetermination typeclass genuinely constraining proof search, or is it just documentation?

3. **Is the sorry-bypass gap (FormalisationBoundary.formal sorry) a fatal flaw?** The paper acknowledges this. But does it undermine the entire contribution? What would a stronger design look like?

4. **What properties SHOULD be proven that are missing?** If you were extending this work, what would the next 5 theorems be? What would make the formalisation genuinely useful (not just an academic exercise)?

5. **How does this compare to DDL, Catala, L4L, and LegalRuleML?** Is the comparison fair? Are there systems the paper fails to compare against? Is the claim of superiority on 7 dimensions justified or self-serving?

6. **Is the monotonicity break theorem genuinely non-trivial?** The proof is two `simp` calls. The paper argues the non-triviality is in the universality. Is this convincing?

7. **Would this paper be accepted at JURIX 2026?** Rate: Strong Accept / Accept / Weak Accept / Borderline / Weak Reject / Reject / Strong Reject. Justify with specific strengths and weaknesses.

8. **What is the single most important improvement that would strengthen this work?**

## Important Context

- The paper is honest about limitations (Section 5.3). Judge whether the honesty is genuine or performative.
- The comparison table scores were self-assessed and the paper acknowledges potential bias.
- The case studies encode selected provisions, not complete statutes.
- The author is a CTO at a legal AI company, not a full-time academic. Judge the work on its merits, not the author's pedigree.

## Files Provided

You will receive:
- The paper (verified-legal-reasoning.md)
- Core framework types (Core.lean)
- The IRC §163(h) case study with theorems (IRC163h.lean + Theorems.lean)
- The O-1 Visa case study (O1Visa.lean)

Read all files carefully before responding. Your review should reference specific lines, theorem names, and code constructs.

---

# SOURCE FILES

## File: LegalLean/Core.lean

```lean
/-
  LegalLean.Core — Foundation types for verified legal reasoning.

  Architecture: LLMs are heuristic transducers (messy input → structured form);
  Lean 4 is the invariant verifier (checks the logic).

  Key types:
  - `Deontic`: permitted / prohibited / obligatory
  - `LegalRule`: a rule with defeasibility metadata
  - `EvidenceFor`: propositions-as-types for legal evidence
  - `FormalisationBoundary`: Hart's open texture as a first-class type

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
-/

namespace LegalLean

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
  authority : String

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
  /-- Requires human determination: annotated with why. -/
  | boundary (reason : String) (authority : String) : FormalisationBoundary P
  /-- Mixed: partially formal, partially human. The `formalPart` is verified;
      the `humanPart` is annotated. -/
  | mixed (formalPart : String) (humanPart : String) : FormalisationBoundary P

end LegalLean
```

## File: LegalLean/CaseStudies/IRC163h.lean

```lean
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

/-- An indebtedness with provenance and amount. -/
structure Indebtedness where
  id : String
  amount : Cents
  dateIncurred : String       -- ISO 8601
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
    Encoded as a decidable proposition over the dateIncurred string.
    In a full system this would use a proper date type with ordering. -/
def preTRA87 (debt : Indebtedness) : Prop :=
  -- We encode this as: the dateIncurred string is lexicographically ≤ "1987-10-13".
  -- This works because ISO 8601 dates sort lexicographically.
  debt.dateIncurred ≤ "1987-10-13"

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
    Case law: Bolton, Glicksman, Robinson v. Commissioner. -/
axiom IsQualifiedResidence : Indebtedness → Prop

variable (debt : Indebtedness) in
instance : LegalLean.Vague (IsQualifiedResidence debt) where
  reason := "IRC §163(h)(4)(A): 'qualified residence' requires property to be " ++
            "'used as a residence' — penumbral cases include mobile homes, " ++
            "timeshares, boats with sleeping/cooking/toilet facilities"
  authority := "IRS / Tax Court"
  core := "Taxpayer's principal residence and one other property " ++
          "used as a residence during the taxable year"
  penumbra := "Vacation homes used <14 days/year, partial-year use, " ++
              "inherited homes not personally occupied, fractional ownership, " ++
              "boats/RVs meeting habitability requirements"

/-- "Substantially improve" — vague term in acquisition indebtedness definition.
    Core: additions, major renovations increasing value or extending useful life.
    Penumbra: minor remodelling, landscaping, appliance replacement.
    Case law: Fackler, Tschetschot v. Commissioner. -/
axiom IsSubstantialImprovement : Indebtedness → Prop

variable (debt : Indebtedness) in
instance : LegalLean.Vague (IsSubstantialImprovement debt) where
  reason := "IRC §163(h)(3)(B): 'substantially improve' is not defined in the " ++
            "statute — must be determined case-by-case"
  authority := "IRS / Tax Court"
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
  authority := "IRS"
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
          "IRS / Tax Court"
    | IndebtednessPurpose.other =>
        LegalLean.FormalisationBoundary.boundary
          "Not acquisition purpose — may be home equity"
          "IRS"
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
    and explicitly marks where human determination is required. -/
def isDeductible
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    : FormalisationBoundary Prop :=
  -- Step 1: Check formalisable conditions
  if ¬payment.paidByIndividual then
    FormalisationBoundary.formal False  -- C1.2 fails: not individual
  else if ¬payment.indebtedness.securedByResidence then
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
          "IRS / Tax Court"
      else
        FormalisationBoundary.boundary
          ("Acquisition limit exceeded. Check if pre-October 13, 1987 " ++
           "grandfather rule (R3) applies.")
          "IRS / Tax Court"
    | IndebtednessPurpose.substantiallyImprove =>
      FormalisationBoundary.boundary
        ("Classification depends on whether improvements constitute " ++
         "'substantial improvement' — requires IRS/Tax Court determination")
        "IRS / Tax Court"
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
            "IRS / Tax Court"
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
```

## File: LegalLean/CaseStudies/IRC163h/Theorems.lean

```lean
/-
  LegalLean.CaseStudies.IRC163h.Theorems — Substantive properties of IRC §163(h).

  These theorems are the monograph's claimed contributions for this case study.
  Each supports a specific thesis component (T1–T5) and says something a legal
  scholar would find non-trivial.

  Unlike the previous "unit test" theorems (which just traced code paths),
  these prove structural properties about the *legal domain* that could not
  be verified by running the function on examples.

  Monograph chapter: "Case Study 1: IRC §163(h) Mortgage Interest Deduction"
-/

import LegalLean.Core
import LegalLean.Defeasible
import LegalLean.CaseStudies.IRC163h

open LegalLean
open LegalLean.CaseStudies.IRC163h

namespace Theorems

-- ============================================================
-- T2: Defeasibility is non-monotonic
-- "Adding a rule can REMOVE a conclusion"
-- ============================================================

/-- Theorem (T2-supporting): Direct defeat acyclicity.
    No rule in IRC §163(h) directly defeats itself.
    This is a necessary condition for the defeat relation to be well-founded.

    Why this matters for the monograph: proves the defeat graph we extracted
    from the statute is structurally sound. A cycle would mean a rule
    simultaneously applies and doesn't apply — a contradiction in the
    legal system itself (not just our encoding). -/
theorem defeat_direct_acyclicity :
    ∀ d ∈ allDefeats, d.defeater ≠ d.defeated := by
  intro d hd
  simp [allDefeats] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [defeat_R2_R1, defeat_E1_1_R1, defeat_E1_2_R1, defeat_R3_E1_1]

/-- Theorem (T2-supporting): The defeat chain has depth exactly 2.
    R3 defeats E1.1 which defeats R1, but R3 does not directly defeat R1.
    This demonstrates that defeat resolution requires transitive reasoning.

    Why this matters: shows that a simple "flat" priority ordering is
    insufficient — the defeat structure has genuine depth, which is why
    Reiter's default logic (Lawsky 2017) is the right framework. -/
theorem defeat_chain_exists :
    ∃ d1 d2 : Defeats,
      d1 ∈ allDefeats ∧ d2 ∈ allDefeats ∧
      d1.defeater = "R3" ∧ d1.defeated = "E1.1" ∧
      d2.defeater = "E1.1" ∧ d2.defeated = "R1" := by
  exact ⟨defeat_R3_E1_1, defeat_E1_1_R1,
    ⟨by simp [allDefeats], by simp [allDefeats],
     rfl, rfl, rfl, rfl⟩⟩

/-- Theorem (T2-supporting): R3 does NOT directly defeat R1.
    The grandfather clause exempts from the dollar LIMIT (E1.1),
    not from the base rule itself. This is a legally meaningful
    distinction: grandfathered debt still must be qualified residence
    interest (R1's conditions), just not subject to E1.1's dollar cap.

    Why this matters: proves our defeat graph captures a genuine
    legal subtlety — not just "R3 overrides everything" but
    "R3 specifically neutralises E1.1". -/
theorem grandfather_does_not_directly_defeat_base :
    ∀ d ∈ allDefeats, d.defeater = "R3" → d.defeated ≠ "R1" := by
  intro d hd hdefeater
  simp [allDefeats] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [defeat_R2_R1, defeat_E1_1_R1, defeat_E1_2_R1, defeat_R3_E1_1]

-- ============================================================
-- T2 + T3: Deontic consistency
-- "No payment is simultaneously permitted AND prohibited"
-- ============================================================

/-- Theorem (T2+T3 supporting): TCJA and base rule are deontic opposites.
    R1 permits; R2 prohibits. The modalities are distinct.

    Why this matters: the statute itself contains a deontic conflict
    (pre-TCJA: permitted; post-TCJA: prohibited for home equity).
    Our encoding preserves this conflict rather than silently resolving it.
    Resolution happens through defeat, not through flattening the modalities. -/
theorem R1_R2_deontic_conflict :
    R1_BaseDeduction.modality ≠ R2_TCJAProhibition.modality := by
  simp [R1_BaseDeduction, R2_TCJAProhibition]

/-- Theorem (T2+T3 supporting): The TCJA prohibition only applies post-2017.
    For any payment where year < 2018, R2's conclusion does not hold
    (because postTCJA is false).

    Why this matters: temporal scoping. The same statute has different
    legal consequences depending on when the payment occurs.
    Our encoding makes this explicit and machine-checkable. -/
theorem pre_tcja_no_prohibition
    (payment : InterestPayment)
    (h_year : payment.taxYear.year < 2018)
    : ¬(isHomeEquityIndebtedness payment.indebtedness ∧ postTCJA payment.taxYear) := by
  intro ⟨_, h_post⟩
  simp [postTCJA] at h_post
  omega

-- ============================================================
-- T3: FormalisationBoundary is meaningful (not just annotations)
-- "The boundary constrains what can be proven"
-- ============================================================

/-- Predicate: a FormalisationBoundary value was constructed with .mixed -/
def isMixedOutcome {P : Sort _} : FormalisationBoundary P → Prop
  | FormalisationBoundary.mixed _ _ => True
  | _ => False

/-- Theorem (T3-supporting): Every code path through isDeductible terminates
    in either `formal` or `boundary` — never `mixed`.

    Why this matters: for this case study, the formalisation boundary is
    binary — either we can decide fully (formal False) or we need human
    input (boundary). There are no partially-formal cases in IRC §163(h).
    This is a structural property of the STATUTE, not just our encoding.

    Proof strategy: unfold isDeductible, case-split on all Bool/enum
    branches, and show each path constructs either .formal or .boundary. -/
theorem no_mixed_outcomes
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    : ¬isMixedOutcome (isDeductible payment year status) := by
  simp only [isDeductible, isMixedOutcome]
  cases payment.paidByIndividual <;> simp
  cases payment.indebtedness.securedByResidence <;> simp
  cases payment.indebtedness.purpose <;> simp
  -- acquire/construct: split on withinAcquisitionLimit
  all_goals (try (cases withinAcquisitionLimit payment.indebtedness year status <;> simp))
  -- other: the remaining goal is ¬(match (if ... then ... else ...) with | mixed => True | _ => False)
  -- We need to reduce the if-then-else first, then match sees formal/boundary
  · -- withinHomeEquityLimit = true case
    cases Nat.decLe 2018 year.year with
    | isTrue h => simp [h]
    | isFalse h => simp [h]; cases withinHomeEquityLimit payment.indebtedness status <;> simp

/-- Theorem (T3-supporting): All boundary annotations in isDeductible
    reference "IRS / Tax Court" as the authority.

    This connects our TYPE SYSTEM to HART'S PHILOSOPHY. It proves
    that the FormalisationBoundary annotations are not arbitrary —
    they all point to the same institutional authority responsible
    for resolving open texture in this statute.

    Proof strategy: case-split on all paths that produce .boundary,
    and verify the authority string. -/
theorem boundary_authority_is_irs_tax_court
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (r a : String)
    (h_individual : payment.paidByIndividual = true)
    (h_secured : payment.indebtedness.securedByResidence = true)
    (h : isDeductible payment year status = FormalisationBoundary.boundary r a)
    : a = "IRS / Tax Court" := by
  simp [isDeductible, h_individual, h_secured] at h
  cases h_purpose : payment.indebtedness.purpose <;> simp [h_purpose] at h
  · -- acquire: split on limit check
    split at h <;> simp_all
  · -- construct: split on limit check
    split at h <;> simp_all
  · -- substantiallyImprove: always boundary
    simp_all
  · -- other: split on year
    split at h
    · -- year ≥ 2018: formal False, contradicts h
      simp_all
    · -- year < 2018: split on limit check
      split at h <;> simp_all

-- ============================================================
-- T1: Dependent types encode eligibility (propositions-as-types)
-- ============================================================

/-- Theorem (T1-supporting): The deduction rules form a complete
    partition of the deontic space for this provision.
    Every rule is either permitted or prohibited — no rule is obligatory.
    (Mortgage interest deduction is a permission, not an obligation.)

    Why this matters: validates that our deontic encoding matches the
    statute's actual normative structure. Tax deductions are permissions
    (you MAY deduct), not obligations (you MUST deduct). -/
theorem all_rules_are_permissions_or_prohibitions :
    R1_BaseDeduction.modality ∈ [Deontic.permitted, Deontic.prohibited] ∧
    R2_TCJAProhibition.modality ∈ [Deontic.permitted, Deontic.prohibited] ∧
    R3_GrandfatherRule.modality ∈ [Deontic.permitted, Deontic.prohibited] := by
  simp [R1_BaseDeduction, R2_TCJAProhibition, R3_GrandfatherRule]

/-- Theorem (T1+T3 supporting): Formal False outcomes are exactly the
    automatically-rejectable cases. When isDeductible returns `formal False`,
    the type checker alone determined non-deductibility — no human needed.

    We prove the forward direction: these three conditions each
    independently guarantee automatic rejection. -/
theorem auto_reject_conditions
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    : (payment.paidByIndividual = false →
        isDeductible payment year status = FormalisationBoundary.formal False) ∧
      (payment.indebtedness.securedByResidence = false →
        isDeductible payment year status = FormalisationBoundary.formal False) ∧
      (payment.indebtedness.purpose = IndebtednessPurpose.other →
       year.year ≥ 2018 →
       payment.paidByIndividual = true →
       payment.indebtedness.securedByResidence = true →
        isDeductible payment year status = FormalisationBoundary.formal False) := by
  refine ⟨fun h => ?_, fun h => ?_, fun hp hy hi hs => ?_⟩
  · simp [isDeductible, h]
  · simp [isDeductible]
    cases payment.paidByIndividual <;> simp [h]
  · simp [isDeductible, hi, hs, hp, hy]

-- ============================================================
-- T2: THE MONOTONICITY BREAK THEOREM
-- "Adding a rule REMOVES a conclusion"
-- This is the monograph's most important proof.
-- ============================================================

/-- A concrete home equity payment: individual taxpayer, secured debt,
    purpose = other (home equity), amount within limits ($50,000). -/
def sampleHomeEquityDebt : Indebtedness where
  id := "HE-001"
  amount := 5000000  -- $50,000 (in cents)
  dateIncurred := "2015-06-15"
  securedByResidence := true
  residenceType := Option.some ResidenceType.principalResidence
  purpose := IndebtednessPurpose.other

def samplePayment : InterestPayment where
  indebtedness := sampleHomeEquityDebt
  amount := 300000  -- $3,000 annual interest
  taxYear := ⟨2017⟩  -- Pre-TCJA (will be overridden in theorems)
  paidByIndividual := true

/-- Theorem (T2 — THE KEY THEOREM): Monotonicity break.

    The SAME home equity payment is potentially deductible in 2017
    (returns FormalisationBoundary.boundary — needs human review of
    "qualified residence") but DEFINITELY NOT deductible in 2018
    (returns FormalisationBoundary.formal False — machine-verified
    rejection due to TCJA).

    This is the defining property of NON-MONOTONIC reasoning:
    adding a rule (TCJA 2017) to the legal system REMOVES a
    previously valid conclusion (home equity interest deduction).

    In monotonic logic, adding premises can only ADD conclusions.
    In legal reasoning, new statutes can RETRACT existing permissions.
    Our encoding captures this, and Lean 4 verifies it.

    Why this matters for the monograph:
    - Proves our encoding of defeasibility actually DEFEATS
    - Demonstrates that dependent types capture legal dynamics
    - No prior work has a machine-checked proof of statutory
      monotonicity break for a real provision
    - Directly addresses the strongest counterargument: "this is
      just type definitions with trivial proofs" — this theorem
      requires reasoning about two different legal regimes and
      proving they yield different outcomes for identical facts -/
theorem monotonicity_break_tcja :
    -- Pre-TCJA (2017): potentially deductible (boundary — needs human on "qualified residence")
    (∃ r a, isDeductible samplePayment ⟨2017⟩ FilingStatus.single =
              FormalisationBoundary.boundary r a) ∧
    -- Post-TCJA (2018): definitely NOT deductible (formal False — machine-verified)
    (isDeductible samplePayment ⟨2018⟩ FilingStatus.single =
              FormalisationBoundary.formal False) := by
  constructor
  · -- Pre-TCJA: show the function returns .boundary for year=2017
    -- Path: paidByIndividual=true → securedByResidence=true → purpose=other
    --       → year < 2018 → withinHomeEquityLimit=true → boundary
    exact ⟨_, _, rfl⟩
  · -- Post-TCJA: show the function returns .formal False for year=2018
    -- Path: paidByIndividual=true → securedByResidence=true → purpose=other
    --       → year ≥ 2018 → formal False (TCJA defeats)
    rfl

/-- Theorem (T2 — generalised monotonicity break):
    For ANY home equity payment by an individual on secured property
    within limits, the legal outcome changes at the 2018 boundary.

    Pre-TCJA: the system reaches the formalisation boundary
    (human must determine "qualified residence").
    Post-TCJA: the system rejects automatically
    (TCJA defeats the deduction permission).

    This is the GENERALISED version — not just for our sample payment,
    but for ALL payments satisfying the home equity conditions. -/
theorem monotonicity_break_general
    (payment : InterestPayment)
    (status : FilingStatus)
    (h_individual : payment.paidByIndividual = true)
    (h_secured : payment.indebtedness.securedByResidence = true)
    (h_purpose : payment.indebtedness.purpose = IndebtednessPurpose.other)
    (h_within : withinHomeEquityLimit payment.indebtedness status = true)
    -- Pre-TCJA: boundary (potentially deductible, needs human)
    : (∃ r a, isDeductible payment ⟨2017⟩ status =
                FormalisationBoundary.boundary r a) ∧
    -- Post-TCJA: formal False (automatically rejected)
      (isDeductible payment ⟨2018⟩ status =
                FormalisationBoundary.formal False) := by
  constructor
  · -- Pre-TCJA
    simp [isDeductible, h_individual, h_secured, h_purpose, h_within]
  · -- Post-TCJA
    simp [isDeductible, h_individual, h_secured, h_purpose]

/-- Corollary: The monotonicity break is STRICT — not just a change
    in outcome, but a change from "possibly permitted" to "certainly
    prohibited." The pre-TCJA outcome is NOT formal False. -/
theorem pre_tcja_not_auto_rejected
    (payment : InterestPayment)
    (status : FilingStatus)
    (h_individual : payment.paidByIndividual = true)
    (h_secured : payment.indebtedness.securedByResidence = true)
    (h_purpose : payment.indebtedness.purpose = IndebtednessPurpose.other)
    (h_within : withinHomeEquityLimit payment.indebtedness status = true)
    : isDeductible payment ⟨2017⟩ status ≠ FormalisationBoundary.formal False := by
  simp [isDeductible, h_individual, h_secured, h_purpose, h_within]

end Theorems
```

## File: LegalLean/CaseStudies/O1Visa.lean

```lean
/-
  LegalLean.CaseStudies.O1Visa — O-1A Visa "3 of 8" Criteria.

  The primary case study. Personally relevant (Eduardo's own application),
  rich rule/discretion mix, and "3 of 8" is a natural dependent type problem.

  The O-1A visa (8 CFR § 204.5(h)) requires demonstrating "extraordinary
  ability" by meeting at least 3 of 8 evidentiary criteria. This is a
  canonical [standard-form] dependent type problem:
  `MeetsThreeCriteria` is a type that can only be inhabited if you can
  construct evidence for at least 3 distinct criteria from the statutory list.

  Key challenge: each criterion involves both:
  - Formalisable elements (document counts, membership lists)
  - Open texture requiring USCIS adjudicator discretion ("sustained national
    or international acclaim", "extraordinary ability", "comparable evidence")

  Source: 8 CFR § 204.5(h)
  Key case law:
  - Kazarian v. USCIS, 596 F.3d 1115 (9th Cir. 2010): two-part framework
    (meet criteria count, then final merits determination)
  - Rijal v. USCIS: comparable evidence scope

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
  No Mathlib dependency: Finset avoided; cardinality encoded via List.length.
-/

import LegalLean.Core
import LegalLean.Defeasible

namespace LegalLean.CaseStudies.O1Visa

-- ============================================================
-- Domain types: the entities and predicates of 8 CFR § 204.5(h)
-- ============================================================

/-- The eight evidentiary criteria under 8 CFR § 204.5(h)(3).
    Encoded as an inductive with decidable equality so we can form
    duplicate-free lists and reason about their length ≥ 3. -/
inductive Criterion where
  /-- C1: Receipt of nationally/internationally recognised prize or award
      for excellence in the field. -/
  | majorAward          : Criterion
  /-- C2: Membership in associations requiring outstanding achievement
      as judged by recognised national or international experts. -/
  | membership          : Criterion
  /-- C3: Published material in professional or major trade publications
      or other major media about the person and their work. -/
  | mediaCoverage       : Criterion
  /-- C4: Participation as a judge of the work of others, either
      individually or on a panel. -/
  | judgingRole         : Criterion
  /-- C5: Original scientific, scholarly, artistic, athletic, or
      business-related contributions of major significance in the field. -/
  | originalContribs    : Criterion
  /-- C6: Authorship of scholarly articles in the field in professional
      or major trade publications or other major media. -/
  | scholarlyAuthorship : Criterion
  /-- C7: Employment in a critical or essential capacity for organisations
      and establishments that have a distinguished reputation. -/
  | criticalEmployment  : Criterion
  /-- C8: Commanded a high salary or other significantly high remuneration
      for services, in relation to others in the field. -/
  | highSalary          : Criterion
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An applicant record. Kept abstract so the case study compiles against
    the existing Core types. -/
structure Applicant where
  id : String
  deriving Repr

/-- A publication record (for criteria C3 and C6). -/
structure Publication where
  id : String
  /-- Whether the outlet is recorded as a major/professional publication
      (formalisable part; which outlets qualify is discretionary). -/
  isRecordedAsMajor : Bool
  deriving Repr

/-- An award record (for criterion C1). -/
structure Award where
  id : String
  /-- Whether the award is recorded as nationally/internationally recognised
      (formalisable part; prestige threshold is discretionary). -/
  isRecordedAsRecognised : Bool
  deriving Repr

-- ============================================================
-- Helper: duplicate-free list (NoDup analogue without Mathlib)
-- ============================================================

/-- `AllDistinct xs` holds when no element appears twice in `xs`.
    This is our replacement for `Finset.card` — we encode the set of
    satisfied criteria as a list that is duplicate-free, so `List.length`
    equals the cardinality. -/
inductive AllDistinct {α : Type} [DecidableEq α] : List α → Prop
  | nil  : AllDistinct []
  | cons : ∀ {x : α} {xs : List α}, x ∉ xs → AllDistinct xs → AllDistinct (x :: xs)

/-- Decidable instance for AllDistinct, derived from decidability of list membership
    and the inductive structure. -/
def decidableAllDistinct {α : Type} [DecidableEq α] : ∀ (xs : List α), Decidable (AllDistinct xs)
  | [] => isTrue AllDistinct.nil
  | x :: xs =>
    match decidableAllDistinct xs with
    | isFalse h => isFalse (fun ad => by cases ad with | cons _ htail => exact h htail)
    | isTrue htail =>
      match (inferInstance : Decidable (x ∈ xs)) with
      | isTrue hmem  => isFalse (fun ad => by cases ad with | cons hni _ => exact hni hmem)
      | isFalse hni  => isTrue (AllDistinct.cons hni htail)

instance {α : Type} [DecidableEq α] (xs : List α) : Decidable (AllDistinct xs) :=
  decidableAllDistinct xs

-- ============================================================
-- Formalisable conditions (type checker can verify these)
-- ============================================================

/-- C4 (formal part): Has held at least one judging role. -/
def hasJudgingRole (roleCount : Nat) : Prop := roleCount ≥ 1

/-- C6 (formal part): Has authored at least one article recorded as
    being in a professional/major outlet. -/
def hasScholarlyArticle (articles : List Publication) : Prop :=
  articles.any (fun p => p.isRecordedAsMajor) = true

/-- C3 (formal part): Has at least one recorded media mention. -/
def hasMediaCoverage (mentions : List Publication) : Prop :=
  mentions.any (fun p => p.isRecordedAsMajor) = true

/-- C1 (formal part): Has at least one recorded qualifying award. -/
def hasQualifyingAward (awards : List Award) : Prop :=
  awards.any (fun a => a.isRecordedAsRecognised) = true

-- ============================================================
-- Open texture: propositions requiring human determination
-- FormalisationBoundary marks WHERE the type checker must stop
-- ============================================================

/-- "Extraordinary ability" — the overarching standard.
    Core (Vague): Top-tier expertise significantly above the ordinary.
    Penumbra: "Very accomplished" vs "extraordinary"; field-relative thresholds.
    Case law: Kazarian v. USCIS (9th Cir. 2010). -/
axiom HasExtraordinaryAbility : Applicant → Prop

variable (a : Applicant) in
instance vague_extraordinary : LegalLean.Vague (HasExtraordinaryAbility a) where
  reason := "8 CFR § 204.5(h)(2): 'extraordinary ability' means a level of expertise " ++
            "significantly above that ordinarily encountered — inherently comparative " ++
            "and field-relative, not reducible to a decision procedure"
  authority := "USCIS adjudicator (AAO appealable)"
  core := "Nobel laureates, Olympic medalists, field-leading researchers with " ++
          "major awards and consistent multi-year international recognition"
  penumbra := "Boundary between 'very accomplished' and 'extraordinary'; " ++
              "field-relative standards; weight given to each criterion; " ++
              "sufficiency of combined evidence (Kazarian two-part test)"

/-- "Sustained national or international acclaim" — sub-criterion of the
    extraordinary ability standard.
    Core (Vague): Consistent recognition over 3+ years via multiple channels.
    Penumbra: Duration required? National vs international threshold? -/
axiom HasSustainedAcclaim : Applicant → Prop

variable (a : Applicant) in
instance vague_acclaim : LegalLean.Vague (HasSustainedAcclaim a) where
  reason := "Continued recognition over time at national or international level — " ++
            "duration and geographic scope thresholds are not defined in the statute"
  authority := "USCIS adjudicator"
  core := "Multi-year recognition through major awards, publications, and media coverage"
  penumbra := "Short-term vs sustained? Recent vs historical acclaim? " ++
              "National recognition sufficient when international not established?"

/-- C1: Award prestige is nationally/internationally recognised.
    The existence of an award is formalisable; its prestige level is not.
    Vague: "recognised" has a clear core (Nobel, Turing) and a penumbra
    (industry prizes, regional honours). -/
axiom AwardIsRecognised : Award → Prop

variable (aw : Award) in
instance vague_award : LegalLean.Vague (AwardIsRecognised aw) where
  reason := "'Nationally or internationally recognized prize or award for excellence' " ++
            "— no statutory threshold for prestige level"
  authority := "USCIS adjudicator"
  core := "Nobel Prize, Fields Medal, Olympic gold medal, Turing Award"
  penumbra := "Industry prizes, regional academic honours, internal company awards, " ++
              "competitive grants; USCIS may weigh multiple minor awards cumulatively"

/-- C2: Association outstanding-achievement membership standard.
    Membership is formalisable; whether the association "requires outstanding
    achievement as judged by recognised experts" is discretionary. -/
axiom AssociationRequiresOutstanding : String → Prop  -- String = association name

variable (assocName : String) in
instance disc_membership : LegalLean.Discretionary (AssociationRequiresOutstanding assocName) where
  reason := "Whether the association's membership criteria constitute " ++
            "'outstanding achievement as judged by recognized national or " ++
            "international experts' is not defined by a bright-line rule"
  authority := "USCIS adjudicator"
  scope := "Determination of whether association membership standards are " ++
           "sufficiently selective and expert-judged"
  constraints := [
    "Must be judged by recognised national or international experts",
    "Self-certification or automatic membership disqualifies",
    "Must be in the applicant's field of extraordinary ability"
  ]

/-- C5: Contributions of major significance in the field.
    The existence of contributions is formalisable; "major significance" is not.
    Discretionary: weight depends on expert letters and adjudicator judgment. -/
axiom ContributionsAreMajor : Applicant → Prop

variable (a : Applicant) in
instance disc_contribs : LegalLean.Discretionary (ContributionsAreMajor a) where
  reason := "'Original scientific, scholarly, or business-related contributions " ++
            "of major significance' — significance is entirely fact-specific"
  authority := "USCIS adjudicator"
  scope := "Whether the applicant's contributions have influenced the field " ++
           "significantly beyond routine professional work"
  constraints := [
    "Must be supported by expert letters explaining specific impact",
    "Mere authorship or patents insufficient without demonstrated uptake",
    "Field-relative standard; 'major' in a small field may differ from a large one"
  ]

/-- C7: Critical or essential capacity at a distinguished organisation.
    Employment is formalisable; "critical/essential" and "distinguished" are not.
    Both terms are Vague (core clear, penumbra contested). -/
axiom RoleIsCriticalAtDistinguished : Applicant → String → Prop  -- String = org name

variable (a : Applicant) (orgName : String) in
instance vague_employment : LegalLean.Vague (RoleIsCriticalAtDistinguished a orgName) where
  reason := "'Critical or essential capacity' and 'distinguished reputation' are " ++
            "both undefined — require adjudicator evaluation of role scope and org standing"
  authority := "USCIS adjudicator"
  core := "CEO/CTO of a Fortune 500 company; lead researcher at a top-tier university"
  penumbra := "Mid-level technical roles; organisations with regional but not national " ++
              "reputation; whether 'critical' means indispensable or merely important"

/-- C8: High salary relative to others in the field.
    "High" is explicitly field-relative and lacks a statutory threshold.
    Vague: clear core (top 1% of field), contested penumbra (top 20%?). -/
axiom SalaryIsHigh : Applicant → Prop

variable (a : Applicant) in
instance vague_salary : LegalLean.Vague (SalaryIsHigh a) where
  reason := "'High salary or other significantly high remuneration in relation " ++
            "to others in the field' — no numerical threshold; field-relative"
  authority := "USCIS adjudicator"
  core := "Salary documented in top 5–10% of field via BLS or salary surveys"
  penumbra := "Equity compensation, deferred pay, or non-monetary benefits; " ++
              "geographic variation in salary norms; early-career vs senior comparison"

/-- Comparable evidence escape hatch (8 CFR § 204.5(h)(4)).
    When standard criteria do not readily apply to the field, USCIS
    may accept comparable evidence. Fully Discretionary: both the
    determination that criteria do not apply AND the weight given to
    alternatives rest with the adjudicator. -/
axiom ComparableEvidenceApplies : Applicant → Prop

variable (a : Applicant) in
instance disc_comparable : LegalLean.Discretionary (ComparableEvidenceApplies a) where
  reason := "8 CFR § 204.5(h)(4): 'if the above standards do not readily apply " ++
            "to the beneficiary's occupation, the petitioner may submit comparable evidence " ++
            "to establish the beneficiary's eligibility' — complete adjudicator discretion"
  authority := "USCIS adjudicator"
  scope := "Determination that (i) standard criteria do not apply to the field AND " ++
           "(ii) the comparable evidence demonstrates extraordinary ability at equivalent weight"
  constraints := [
    "Must be comparable in import, relevance, and weight to listed criteria",
    "Petitioner bears burden of explaining why standard criteria do not apply",
    "Rijal v. USCIS: comparable evidence must still meet same substantive threshold"
  ]

-- ============================================================
-- The 8-criterion satisfaction type
-- Each criterion maps to a Prop; evidence is EvidenceFor that Prop
-- ============================================================

/-- Per-criterion axioms: each O-1A criterion maps to its own distinct
    open-texture proposition. This preserves per-criterion resolution
    (a reviewer can verify that each criterion's Vague/Discretionary
    instance is independently justified). -/
axiom MeetsAwardCriterion : Applicant → Prop           -- (i) major awards/prizes
axiom MeetsMembershipCriterion : Applicant → Prop       -- (ii) membership in associations
axiom MeetsMediaCriterion : Applicant → Prop            -- (iii) published material about the applicant
axiom MeetsJudgingCriterion : Applicant → Prop          -- (iv) judging the work of others
axiom MeetsScholarlyAuthorshipCriterion : Applicant → Prop  -- (vi) authorship of scholarly articles
axiom MeetsCriticalEmploymentCriterion : Applicant → Prop   -- (vii) critical/essential role

def criterionProp (a : Applicant) (c : Criterion) : Prop :=
  match c with
  | Criterion.majorAward          => MeetsAwardCriterion a
  | Criterion.membership          => MeetsMembershipCriterion a
  | Criterion.mediaCoverage       => MeetsMediaCriterion a
  | Criterion.judgingRole         => MeetsJudgingCriterion a
  | Criterion.originalContribs    => ContributionsAreMajor a
  | Criterion.scholarlyAuthorship => MeetsScholarlyAuthorshipCriterion a
  | Criterion.criticalEmployment  => MeetsCriticalEmploymentCriterion a
  | Criterion.highSalary          => SalaryIsHigh a

-- ============================================================
-- The "3 of 8" dependent type: MeetsThreeCriteria
-- Cardinality encoded via AllDistinct + List.length ≥ 3
-- (avoids Mathlib.Data.Finset dependency)
-- ============================================================

/-- Part 1 (Kazarian): Meets at least 3 of the 8 evidentiary criteria.
    `satisfied` is a duplicate-free list of criteria the applicant evidenced.
    `distinct` proves no criterion is listed twice (so length = cardinality).
    `cardinal` proves length ≥ 3.
    `evidence` maps each element to an EvidenceFor its Prop.

    This structure CAN ONLY BE INHABITED if the applicant genuinely has
    evidence for ≥ 3 distinct criteria — Lean enforces this at compile time. -/
structure MeetsThreeCriteria (a : Applicant) where
  /-- The duplicate-free list of criteria the applicant has satisfied. -/
  satisfied : List Criterion
  /-- No criterion appears twice. -/
  distinct  : AllDistinct satisfied
  /-- At least 3 criteria must be met (cardinality constraint). -/
  cardinal  : satisfied.length ≥ 3
  /-- For each satisfied criterion, a proof witness (EvidenceFor its Prop). -/
  evidence  : ∀ c ∈ satisfied, LegalLean.EvidenceFor (criterionProp a c)

/-- Part 2 (Kazarian): Final merits determination.
    Even after meeting ≥ 3 criteria, USCIS conducts a holistic assessment
    of whether the totality of evidence demonstrates extraordinary ability.
    This is fully at the formalisation boundary — not machine-verifiable. -/
def finalMeritsDetermination (_a : Applicant)
    : LegalLean.FormalisationBoundary Prop :=
  LegalLean.FormalisationBoundary.boundary
    ("Kazarian v. USCIS: meeting ≥ 3 criteria is necessary but not sufficient. " ++
     "USCIS must then determine whether the totality of evidence demonstrates " ++
     "extraordinary ability at the level of sustained national/international acclaim.")
    "USCIS adjudicator (AAO appealable)"

/-- Full O-1A eligibility: BOTH parts of the Kazarian two-part test.
    Part 1 is formalisable (AllDistinct list with length ≥ 3).
    Part 2 is at the formalisation boundary (holistic merits). -/
structure EligibleO1A (a : Applicant) where
  /-- Part 1 (formalisable): at least 3 distinct criteria met with evidence. -/
  part1 : MeetsThreeCriteria a
  /-- Part 2 (boundary): final merits determination by USCIS. -/
  part2 : LegalLean.FormalisationBoundary Prop

-- ============================================================
-- Rules: the defeasible structure of 8 CFR § 204.5(h)
-- ============================================================

/-- R1: Base eligibility rule.
    Applicant is OBLIGATORY to be granted O-1A if they have extraordinary
    ability AND meet at least 3 of 8 criteria. -/
def R1_O1A_BaseEligibility : LegalRule Applicant where
  id := "R1-O1A"
  description := "Applicant is eligible for O-1A classification if they " ++
                 "demonstrate extraordinary ability (sustained national/international " ++
                 "acclaim) and meet at least 3 of 8 criteria in 8 CFR § 204.5(h)(3)"
  modality := Deontic.obligatory
  priority := ⟨1, "regulation (8 CFR § 204.5(h))"⟩
  conclusion := fun a => HasExtraordinaryAbility a
  defeatedBy := ["R2-ComparableEvidence"]

/-- R2: Comparable evidence alternative (lex specialis [more specific rule
    overrides general one]).
    When standard criteria do not readily apply to the field, comparable
    evidence may substitute — but only with USCIS approval. -/
def R2_ComparableEvidence : LegalRule Applicant where
  id := "R2-ComparableEvidence"
  description := "When the standard evidentiary criteria do not readily apply " ++
                 "to the applicant's field, comparable evidence may be substituted " ++
                 "(8 CFR § 204.5(h)(4))"
  modality := Deontic.permitted
  priority := ⟨2, "regulation (lex specialis, § 204.5(h)(4))"⟩
  conclusion := fun a => ComparableEvidenceApplies a
  defeatedBy := []

-- ============================================================
-- Defeat relations
-- ============================================================

/-- R2 defeats R1's standard-criteria requirement when standard criteria
    are inapplicable to the field. Non-strict: USCIS can still apply
    standard criteria if they fit the field. -/
def defeat_ComparableEvidence_Standard : Defeats where
  defeater := "R2-ComparableEvidence"
  defeated := "R1-O1A"
  reason := "lex specialis: 8 CFR § 204.5(h)(4) provides a specific alternative " ++
            "route when standard criteria do not readily apply"
  strict := false

/-- All defeat relations for this provision. -/
def allDefeats : List Defeats :=
  [defeat_ComparableEvidence_Standard]

-- ============================================================
-- Eligibility determination: composing both parts of Kazarian
-- ============================================================

/-- Determine O-1A eligibility for a given applicant.
    Returns a FormalisationBoundary because Part 2 (final merits) is
    not machine-verifiable. Only Part 1 (criteria count) is formal.

    The function returns `mixed` — the Part 1 result is formally verified
    (Lean checked the length constraint), Part 2 is annotated as requiring
    USCIS adjudicator judgment. -/
def determineEligibility (a : Applicant) (criteria : MeetsThreeCriteria a)
    : FormalisationBoundary Prop :=
  FormalisationBoundary.mixed
    ("Part 1 (Kazarian step 1): applicant has met " ++
     Nat.repr criteria.satisfied.length ++
     " of the 8 criteria — satisfying the ≥ 3 threshold formally verified by Lean")
    ("Part 2 (Kazarian step 2): final merits determination required. " ++
     "USCIS must assess whether the totality of evidence establishes " ++
     "extraordinary ability with sustained national/international acclaim. " ++
     "This is not machine-verifiable (HasExtraordinaryAbility, HasSustainedAcclaim " ++
     "are FormalisationBoundary.boundary propositions).")

-- ============================================================
-- Theorems: properties we want to prove about the formalisation
-- ============================================================

/-- Theorem: An applicant with a MeetsThreeCriteria witness has satisfied
    at least 3 criteria. Direct extraction from the structure's cardinal field. -/
theorem three_criteria_lower_bound (a : Applicant) (w : MeetsThreeCriteria a)
    : w.satisfied.length ≥ 3 := w.cardinal

/-- Theorem: Final merits determination is always at the formalisation boundary.
    The Part 2 result is NEVER `FormalisationBoundary.formal` — it always
    requires the USCIS adjudicator. Proves by `rfl` since `finalMeritsDetermination`
    is a definitionally fixed boundary annotation. -/
theorem final_merits_is_boundary (a : Applicant)
    : ∃ reason authority,
        finalMeritsDetermination a =
          FormalisationBoundary.boundary reason authority :=
  ⟨_, _, rfl⟩

/-- Theorem: R1 and R2 have distinct modalities.
    R1 is obligatory (you MUST be granted the visa if eligible);
    R2 is permitted (the petitioner MAY substitute comparable evidence).
    This deontic distinction is legally meaningful: obligation vs permission. -/
theorem R1_R2_deontic_distinct :
    R1_O1A_BaseEligibility.modality ≠ R2_ComparableEvidence.modality := by
  simp [R1_O1A_BaseEligibility, R2_ComparableEvidence]

/-- Theorem: The defeat relation is not self-defeating (acyclicity).
    No rule in our encoding directly defeats itself — a necessary condition
    for the defeat graph to be well-founded and the legal system consistent. -/
theorem defeat_direct_acyclicity :
    ∀ d ∈ allDefeats, d.defeater ≠ d.defeated := by
  intro d hd
  simp [allDefeats] at hd
  rcases hd with rfl
  simp [defeat_ComparableEvidence_Standard]

/-- Theorem: determineEligibility always returns a `mixed` result.
    This is a structural property of the Kazarian two-part test as encoded:
    whenever a MeetsThreeCriteria witness exists, we can verify Part 1 formally
    but Part 2 is always at the boundary — so the result is always `mixed`,
    never `formal` or `boundary`. -/
theorem eligibility_always_mixed (a : Applicant) (w : MeetsThreeCriteria a)
    : ∃ fp hp,
        determineEligibility a w =
          FormalisationBoundary.mixed fp hp := by
  exact ⟨_, _, rfl⟩

/-- Theorem: An empty list cannot satisfy MeetsThreeCriteria.
    Directly follows from the cardinal field: length [] = 0 < 3. -/
theorem empty_list_ineligible (a : Applicant)
    (w : MeetsThreeCriteria a) : w.satisfied ≠ [] := by
  intro h_empty
  have h_len : w.satisfied.length = 0 := by rw [h_empty]; rfl
  have h_card : w.satisfied.length ≥ 3 := w.cardinal
  omega

-- ============================================================
-- HEADLINE THEOREMS (equivalent depth to IRC163h)
-- ============================================================

/-- Theorem (Monotonicity-like): Adding the comparable evidence route
    CHANGES the normative pathway — it is not additive but substitutive.

    In IRC §163(h) the monotonicity break shows that adding a new rule
    REMOVES a conclusion. Here the analogous result is:
    - R1 is OBLIGATORY (USCIS must grant if criteria met)
    - R2 is PERMITTED (petitioner may substitute comparable evidence)
    - R2 defeates R1's standard-criteria requirement

    Adding comparable evidence does not simply "add a path": it REPLACES
    the obligatory standard-criteria path with a discretionary permitted
    path. The normative consequence changes from obligatory to permitted —
    a genuine non-monotonic shift in legal force.

    This is proved by showing (i) R2 is listed in R1's defeatedBy set
    (structural defeat relation) and (ii) the two rules have distinct
    deontic modalities (obligatory vs permitted). -/
theorem comparable_evidence_changes_pathway :
    ("R2-ComparableEvidence" ∈ R1_O1A_BaseEligibility.defeatedBy) ∧
    (R1_O1A_BaseEligibility.modality = Deontic.obligatory) ∧
    (R2_ComparableEvidence.modality = Deontic.permitted) := by
  simp [R1_O1A_BaseEligibility, R2_ComparableEvidence]

/-- Theorem: An AllDistinct pair implies the two elements are unequal.
    This is the kernel [core mechanism] of the "3 of 8" type: AllDistinct
    prevents any criterion from being counted twice.

    Legal significance: two criteria that are mapped to DIFFERENT axioms
    (e.g. majorAward → MeetsAwardCriterion vs membership → MeetsMembershipCriterion)
    cannot be conflated by listing the same criterion twice. If both appear
    in the `satisfied` list, AllDistinct requires they are distinct values.

    Why this matters: it is not possible to "game" the cardinality requirement
    by listing the same criterion under two different framings — the Criterion
    type has decidable equality and AllDistinct enforces uniqueness. -/
theorem allDistinct_pair_implies_ne
    {α : Type} [DecidableEq α] (x y : α)
    (h : AllDistinct [x, y]) : x ≠ y := by
  cases h with
  | cons hni _ =>
    intro heq
    apply hni
    rw [heq]
    exact List.Mem.head _

/-- Theorem: The statutory eight criteria are pairwise distinct types.
    majorAward and membership map to DIFFERENT axioms (MeetsAwardCriterion
    vs MeetsMembershipCriterion) — they cannot be conflated.

    This uses DecidableEq on Criterion to prove the values are definitionally
    unequal at the type level, ensuring the criterionProp function maps
    them to distinct propositions. -/
theorem majorAward_ne_membership : Criterion.majorAward ≠ Criterion.membership := by
  decide

theorem majorAward_ne_mediaCoverage : Criterion.majorAward ≠ Criterion.mediaCoverage := by
  decide

theorem judgingRole_ne_scholarlyAuthorship
    : Criterion.judgingRole ≠ Criterion.scholarlyAuthorship := by
  decide

/-- Theorem: No MeetsThreeCriteria witness can have a satisfied list of
    length strictly less than 3.

    This is the LOWER BOUND theorem: the dependent type enforces a strict
    cardinality floor [minimum]. A list of length 0, 1, or 2 is definitionally
    insufficient — Lean's type checker refuses to construct MeetsThreeCriteria
    from such a list at compile time.

    The contrapositive is the key insight for visa adjudication: an applicant
    with fewer than 3 criteria documented is AUTOMATICALLY ineligible at Part 1
    of the Kazarian test, without any human judgment needed. This is the only
    fully-formal component of O-1A eligibility. -/
theorem no_witness_below_three (a : Applicant)
    : ¬∃ (w : MeetsThreeCriteria a), w.satisfied.length < 3 := by
  intro ⟨w, h_lt⟩
  have h_ge : w.satisfied.length ≥ 3 := w.cardinal
  omega

/-- Theorem: The cardinality constraint is tight at 3.
    A two-element list cannot satisfy MeetsThreeCriteria regardless of
    which criteria are chosen or what evidence is provided for them.
    This is a direct corollary of no_witness_below_three for length = 2. -/
theorem two_criteria_insufficient (a : Applicant)
    (w : MeetsThreeCriteria a) : w.satisfied.length ≠ 2 := by
  have h_ge : w.satisfied.length ≥ 3 := w.cardinal
  omega

end LegalLean.CaseStudies.O1Visa
```

## File: LegalLean/CaseStudies/TCPCode.lean

```lean
/-
  LegalLean.CaseStudies.TCPCode — Australian Telecommunications Consumer
  Protections Code (C622:2012).

  The third and final case study. Chosen for comparison against Governatori's
  Defeasible Deontic Logic (DDL) encoding of the TCP Code. The key contribution
  of LegalLean over DDL is that dependent types make the FORMALISATION BOUNDARY
  a first-class object: wherever DDL writes a flat defeasible rule, LegalLean
  can tag the boundary between machine-checkable conditions and those requiring
  human determination.

  Scope: three TCP Code provisions (a manageable kernel):
    TCP 3.2  — Contact details obligation (obligatory, lex specialis exception)
    TCP 5.1  — Critical Information Summary obligation (obligatory, renewal exemption)
    TCP 8.2  — Early termination fee prohibition (prohibited, device carve-out)

  Three defeat relations (each lex specialis):
    D1: SmallProviderExemption defeats ContactObligation
    D2: RenewalExemption        defeats CriticalInfoSummary
    D3: DeviceRepaymentCarveout defeats ExcessiveETFProhibited

  Open texture terms (Vague/Discretionary):
    - "reasonable time" (vague): contact update timeliness
    - "prominently published" (vague): layout and visibility
    - "direct costs" (vague): ETF cost allocation
    - "material change" (discretionary): triggers CIS re-provision

  Governatori DDL comparison:
    DDL encodes rules as flat defeasible clauses (r :- p1, p2, not e1).
    LegalLean's advance: the `FormalisationBoundary` type distinguishes
      `formal` (Lean 4 verified), `boundary` (requires ACCC/TIO/court), and
      `mixed` (partial verification). DDL has no such stratification — all
      conditions are treated uniformly as literals that can be included or
      excluded from extensions. Lean's dependent types also allow the
      type of the conclusion to depend on its evidence, which DDL cannot express.

  Source: TCP Code C622:2012 (ACMA registered)
  Reference: Governatori et al., "Compliance in eHealth" (2019);
             Governatori, "Representing Business Contracts in RuleML" (2005).
  Jurisdiction: Australia

  Compatible with Lean 4 v4.24.0. No Mathlib. No Float.
-/

import LegalLean.Core
import LegalLean.Defeasible

namespace LegalLean.CaseStudies.TCPCode

-- ============================================================
-- Domain types: entities and predicates of the TCP Code
-- ============================================================

/-- A telecommunications provider as defined in TCP Code Schedule 1.
    Carriers, carriage service providers (CSPs), and content service providers
    under the Telecommunications Act 1997. -/
structure Provider where
  id : String
  /-- Number of employees (relevant to small-provider exemption). -/
  employeeCount : Nat
  /-- Whether the provider holds a carrier licence under Telecomm. Act 1997. -/
  isLicensed : Bool
  deriving Repr

/-- A consumer: individual acquiring services for personal/domestic use.
    Core meaning is uncontested; penumbra involves small-business customers. -/
structure Consumer where
  id : String
  /-- True if the consumer is an individual (not a corporation). -/
  isIndividual : Bool
  deriving Repr

/-- Contract classification: relevant to CIS and ETF provisions. -/
inductive ContractType where
  /-- Month-to-month (no minimum term). -/
  | monthToMonth
  /-- Fixed-term (has minimum contract period). -/
  | fixedTerm
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A service contract between a provider and consumer. -/
structure ServiceContract where
  id : String
  provider : Provider
  consumer : Consumer
  contractType : ContractType
  /-- Whether this is a renewal of an existing service. -/
  isRenewal : Bool
  /-- Whether the contract terms have materially changed since last CIS. -/
  hasMaterialChange : Bool
  deriving Repr

/-- Contact detail record (for TCP 3.2 obligation). -/
structure ContactDetails where
  hasPostalAddress : Bool
  hasPhoneNumber   : Bool
  hasEmail         : Bool
  hasWebsite       : Bool
  deriving Repr, BEq

/-- A Critical Information Summary document (for TCP 5.1). -/
structure CIS where
  contractId : String
  /-- Whether the CIS follows the ACCC standard format. -/
  isStandardFormat : Bool
  /-- Page count (requirement: ≤ 2 pages). -/
  pageCount : Nat
  deriving Repr

/-- Early termination fee (for TCP 8.2). -/
structure ETF where
  contractId : String
  /-- Amount charged in cents. -/
  amountCents : Nat
  /-- Whether the fee relates solely to device/handset repayment. -/
  isDeviceRepayment : Bool
  deriving Repr

-- ============================================================
-- Formalisable conditions (type checker can verify these)
-- ============================================================

/-- TCP 3.2 C1: Provider is a licensed telecommunications provider. -/
def isLicensedProvider (p : Provider) : Prop :=
  p.isLicensed = true

/-- TCP 3.2 C2: Contact details are structurally complete (all four channels present). -/
def hasCompleteContactDetails (cd : ContactDetails) : Prop :=
  cd.hasPostalAddress = true ∧
  cd.hasPhoneNumber   = true ∧
  cd.hasEmail         = true ∧
  cd.hasWebsite       = true

/-- TCP 3.2 small-provider exemption: fewer than 10 employees.
    This is the lex specialis [more specific rule] that defeats the general
    contact obligation under TCP Code clause 1.6.2. -/
def isSmallProvider (p : Provider) : Prop :=
  p.employeeCount < 10

/-- TCP 5.1 C1: Contract covers a retail consumer service. -/
def isRetailConsumerContract (c : ServiceContract) : Prop :=
  c.consumer.isIndividual = true

/-- TCP 5.1 C3 (formal part): CIS is in standard format and within 2-page limit. -/
def cisIsCompliant (cis : CIS) : Prop :=
  cis.isStandardFormat = true ∧ cis.pageCount ≤ 2

/-- TCP 5.1 renewal exemption: no CIS required for renewals without material change.
    This is the lex specialis that defeats the CIS obligation (TCP 5.1.3). -/
def isExemptRenewal (c : ServiceContract) : Prop :=
  c.isRenewal = true ∧ c.hasMaterialChange = false

/-- TCP 8.2 C1: Contract has a fixed term (ETF prohibition applies). -/
def isFixedTermContract (c : ServiceContract) : Prop :=
  c.contractType = ContractType.fixedTerm

/-- TCP 8.2 device carve-out: fee relates to outstanding device repayment.
    This is the lex specialis exemption under TCP Code clause 8.2.4. -/
def isDeviceRepaymentFee (etf : ETF) : Prop :=
  etf.isDeviceRepayment = true

-- ============================================================
-- Open texture: propositions requiring human determination
-- (FormalisationBoundary marks where the type checker must stop)
-- ============================================================

/-
  The following axioms represent propositions whose truth value
  CANNOT be decided by the Lean 4 type checker alone. They require
  ACCC enforcement assessment, TIO dispute resolution, or court determination.
  This is the honest formalisation of Hart's open texture in the TCP Code.

  Governatori DDL comparison: DDL would write these as ordinary atoms
  (e.g. `prominentlyPublished(p)`) and assert them as facts or leave them
  open. LegalLean instead TYPES the boundary via Vague/Discretionary instances,
  making the need for human determination machine-checkable metadata.
-/

/-- "Prominently published": contact details visible without scrolling,
    adequate font size, contrasting colour. No statutory bright-line rule.
    Vague [core/penumbra distinction exists but penumbra requires judgment].
    Core: top of page, ≥12pt font, high-contrast.
    Penumbra: footer placement, small fonts, low-contrast text. -/
axiom ProminentlyPublished : Provider → Prop

variable (p : Provider) in
instance vague_prominent : LegalLean.Vague (ProminentlyPublished p) where
  reason := "TCP Code 3.2: contact details must be 'prominently published' on " ++
            "all sales materials and websites — no bright-line rule for prominence"
  authority := "ACCC compliance assessment (enforcement discretion)"
  core := "Visible in page header or above the fold; minimum 12pt font; " ++
          "contrasting colour meeting WCAG 2.1 AA accessibility standards"
  penumbra := "Footer placement (common but contested); small font sizes " ++
              "(below 10pt); low-contrast grey-on-white text; mobile vs desktop " ++
              "rendering differences; multi-column layouts where contact info is " ++
              "in a non-primary column"

/-- "Reasonable time" for updating contact details after a change.
    Industry practice benchmark: generally understood as within 30 days,
    but contested for complex re-branding or mergers.
    Vague: 30-day core; multi-month mergers are penumbral. -/
axiom UpdatedWithinReasonableTime : Provider → Prop

variable (p : Provider) in
instance vague_reasonable_time : LegalLean.Vague (UpdatedWithinReasonableTime p) where
  reason := "TCP Code 3.2: contact details must be 'current' — updated within " ++
            "'reasonable time' of change, but no statutory definition of reasonable time"
  authority := "ACCC / TIO dispute resolution (case-by-case)"
  core := "Within 30 days of the change for straightforward updates (new phone, email)"
  penumbra := "Corporate mergers and acquisitions (60–120 days?); " ++
              "regulatory change triggering simultaneous multi-channel updates; " ++
              "whether 'reasonable' tolls during ACMA review periods"

/-- "Direct costs" of early termination: costs directly attributable to the
    consumer's early exit. No bright-line rule for cost allocation.
    Vague: network provisioning costs are clearly included; profit recovery is not.
    Penumbra: customer acquisition costs, marketing attribution. -/
axiom IsWithinDirectCosts : ETF → Prop

variable (etf : ETF) in
instance vague_direct_costs : LegalLean.Vague (IsWithinDirectCosts etf) where
  reason := "TCP Code 8.2: ETF must not exceed 'direct costs' of early termination — " ++
            "'direct costs' is not defined and requires cost allocation methodology"
  authority := "ACCC / TIO / courts (ACCC v Telstra (2016) on ETF methodology)"
  core := "Network provisioning costs directly caused by early exit; " ++
          "unamortised customer premises equipment (CPE) costs within first 6 months"
  penumbra := "Customer acquisition costs (marketing, commissions); " ++
              "opportunity costs of capacity released; lost profit on remaining term; " ++
              "wholesale cost differentials; cross-subsidised handset costs"

/-- "Material change" to service terms triggering a new CIS obligation.
    Discretionary [authority has scope to decide]: provider self-assesses,
    subject to ACCC review. Clear core (price increase >10%); contested penumbra. -/
axiom IsMaterialChange : ServiceContract → Prop

variable (c : ServiceContract) in
instance disc_material_change : LegalLean.Discretionary (IsMaterialChange c) where
  reason := "TCP Code 5.1.3: renewal exemption applies only if there is no " ++
            "'material change' — but the threshold for materiality is not defined"
  authority := "Provider (initial determination) + ACCC (review on complaint)"
  scope := "Provider determines whether changes to price, speed, terms, or bundling " ++
           "constitute a 'material change' triggering the CIS obligation"
  constraints := [
    "Price increases of any amount are presumptively material",
    "New minimum term or revised cancellation rights are material",
    "Speed reductions exceeding 20% are treated as material by ACCC guidance",
    "Provider self-assessment must be consistent with prior determinations",
    "ACCC can override and require CIS provision on complaint"
  ]

-- ============================================================
-- Rules: TCP Code obligations, permissions, and prohibitions
-- ============================================================

/-- R1: Contact details obligation (TCP Code clause 3.2).
    Telecommunications providers are OBLIGATED to maintain and publish
    current, complete contact details.
    Defeated by: SmallProviderExemption (lex specialis, clause 1.6.2). -/
def R1_ContactObligation : LegalRule Provider where
  id := "R1-TCP3.2-ContactObligation"
  description := "TCP Code 3.2: providers must establish, maintain, and prominently " ++
                 "publish current contact details including postal address, phone, " ++
                 "email, and website on all sales materials"
  modality := Deontic.obligatory
  priority := ⟨1, "TCP Code C622:2012 (registered industry code, Telecomm. Act 1997 s. 117)"⟩
  conclusion := fun p =>
    isLicensedProvider p
  defeatedBy := ["R1-TCP3.2-SmallProviderExemption"]

/-- R1-Exemption: Small provider exemption (TCP Code clause 1.6.2).
    Providers with fewer than 10 employees are PERMITTED to use simplified
    contact requirements. Defeats R1 via lex specialis. -/
def R1_SmallProviderExemption : LegalRule Provider where
  id := "R1-TCP3.2-SmallProviderExemption"
  description := "TCP Code 1.6.2: providers with fewer than 10 employees may use " ++
                 "simplified contact requirements (lex specialis exception)"
  modality := Deontic.permitted
  priority := ⟨2, "TCP Code C622:2012 clause 1.6.2 (lex specialis)"⟩
  conclusion := fun p => isSmallProvider p
  defeatedBy := []

/-- R2: Critical Information Summary obligation (TCP Code clause 5.1).
    Providers are OBLIGATED to provide a CIS before the consumer commits
    to a service contract.
    Defeated by: RenewalExemption (lex specialis, clause 5.1.3). -/
def R2_CriticalInfoSummary : LegalRule ServiceContract where
  id := "R2-TCP5.1-CriticalInfoSummary"
  description := "TCP Code 5.1: providers must supply a Critical Information Summary " ++
                 "(ACCC standard format, ≤2 pages) to consumers before they commit " ++
                 "to any retail consumer service contract"
  modality := Deontic.obligatory
  priority := ⟨1, "TCP Code C622:2012 clause 5.1"⟩
  conclusion := fun c => isRetailConsumerContract c
  defeatedBy := ["R2-TCP5.1-RenewalExemption"]

/-- R2-Exemption: Renewal exemption from CIS (TCP Code clause 5.1.3).
    CIS is not required for renewals of existing services without material changes.
    Defeats R2 via lex specialis. -/
def R2_RenewalExemption : LegalRule ServiceContract where
  id := "R2-TCP5.1-RenewalExemption"
  description := "TCP Code 5.1.3: CIS not required for renewals of existing services " ++
                 "where there is no material change to the terms (lex specialis)"
  modality := Deontic.permitted
  priority := ⟨2, "TCP Code C622:2012 clause 5.1.3 (lex specialis)"⟩
  conclusion := fun c => isExemptRenewal c
  defeatedBy := []

/-- R3: Excessive ETF prohibition (TCP Code clause 8.2).
    Providers are PROHIBITED from charging early termination fees that exceed
    the direct costs of early termination.
    Defeated by: DeviceRepaymentCarveout (lex specialis, clause 8.2.4). -/
def R3_ExcessiveETFProhibited : LegalRule ETF where
  id := "R3-TCP8.2-ExcessiveETFProhibited"
  description := "TCP Code 8.2: providers must not charge early termination fees " ++
                 "that exceed the direct costs attributable to the consumer's early exit"
  modality := Deontic.prohibited
  priority := ⟨1, "TCP Code C622:2012 clause 8.2"⟩
  conclusion := fun etf => ¬isDeviceRepaymentFee etf
  defeatedBy := ["R3-TCP8.2-DeviceRepaymentCarveout"]

/-- R3-Carveout: Device repayment carve-out from ETF prohibition (TCP Code clause 8.2.4).
    Outstanding device/handset repayment amounts are excluded from the ETF cap.
    Defeats R3 via lex specialis. -/
def R3_DeviceRepaymentCarveout : LegalRule ETF where
  id := "R3-TCP8.2-DeviceRepaymentCarveout"
  description := "TCP Code 8.2.4: ETF prohibition does not apply to remaining " ++
                 "device/handset repayment under a device payment plan (lex specialis)"
  modality := Deontic.permitted
  priority := ⟨2, "TCP Code C622:2012 clause 8.2.4 (lex specialis)"⟩
  conclusion := fun etf => isDeviceRepaymentFee etf
  defeatedBy := []

-- ============================================================
-- Defeat relations: the non-monotonic structure
-- ============================================================

/-- D1: Small provider exemption defeats general contact obligation.
    Lex specialis [more specific rule overrides general one]: clause 1.6.2 carves out
    providers with <10 employees from the full TCP 3.2 obligation. -/
def defeat_D1_SmallProviderExemption_ContactObligation : Defeats where
  defeater := "R1-TCP3.2-SmallProviderExemption"
  defeated := "R1-TCP3.2-ContactObligation"
  reason := "lex specialis: TCP Code clause 1.6.2 provides a specific exemption for " ++
            "providers with fewer than 10 employees from the full contact obligation"
  strict := true

/-- D2: Renewal exemption defeats CIS obligation.
    Lex specialis: TCP Code clause 5.1.3 exempts renewal contracts without
    material changes from the mandatory CIS provision requirement. -/
def defeat_D2_RenewalExemption_CriticalInfoSummary : Defeats where
  defeater := "R2-TCP5.1-RenewalExemption"
  defeated := "R2-TCP5.1-CriticalInfoSummary"
  reason := "lex specialis: TCP Code clause 5.1.3 exempts renewals without material " ++
            "changes from CIS provision — the exemption is more specific than the rule"
  strict := true

/-- D3: Device repayment carve-out defeats excessive ETF prohibition.
    Lex specialis: TCP Code clause 8.2.4 excludes outstanding device repayment
    from the 'direct costs' cap on ETFs. -/
def defeat_D3_DeviceRepaymentCarveout_ETFProhibited : Defeats where
  defeater := "R3-TCP8.2-DeviceRepaymentCarveout"
  defeated := "R3-TCP8.2-ExcessiveETFProhibited"
  reason := "lex specialis: TCP Code clause 8.2.4 creates a specific carve-out for " ++
            "device repayment amounts from the general ETF direct-costs cap"
  strict := true

/-- All defeat relations for the TCP Code kernel. -/
def allDefeats : List Defeats :=
  [ defeat_D1_SmallProviderExemption_ContactObligation
  , defeat_D2_RenewalExemption_CriticalInfoSummary
  , defeat_D3_DeviceRepaymentCarveout_ETFProhibited
  ]

-- ============================================================
-- Compliance determination functions
-- (composing formal conditions with formalisation boundaries)
-- ============================================================

/-- Determine whether a provider satisfies the TCP 3.2 contact obligation.
    Returns a FormalisationBoundary because "prominently published" and
    "reasonable time" are open-texture conditions the type checker cannot verify.

    Governatori DDL comparison: DDL would express this as a defeasible rule
      r32 :- licensed(P), complete_details(CD), not small_provider(P).
    LegalLean's advance: the `mixed` return value carries both the formally
    verified part (structural completeness of CD) AND a typed annotation
    explaining which condition requires ACCC determination. -/
def assessContactCompliance
    (p : Provider) (cd : ContactDetails)
    : FormalisationBoundary Prop :=
  if !p.isLicensed then
    -- Provider is not subject to TCP Code at all
    FormalisationBoundary.formal False
  else if p.employeeCount < 10 then
    -- D1 applies: small provider exemption defeats the full obligation
    FormalisationBoundary.boundary
      ("Small provider exemption (TCP 1.6.2) applies: provider has " ++
       Nat.repr p.employeeCount ++
       " employees (< 10). Simplified contact requirements permitted.")
      "Provider self-determination (ACCC audit)"
  else
    -- Standard obligation applies: check structural completeness first
    if cd.hasPostalAddress && cd.hasPhoneNumber && cd.hasEmail && cd.hasWebsite then
      -- Structural completeness is formally verified; prominence is not
      FormalisationBoundary.mixed
        ("Contact details are structurally complete (all four channels present: " ++
         "postal address, phone, email, website) — formally verified")
        ("Whether details are 'prominently published' (TCP 3.2) and " ++
         "'current' (updated within reasonable time) requires ACCC assessment")
    else
      -- Structural completeness fails — formally verified non-compliance
      FormalisationBoundary.formal False

/-- Determine whether the CIS obligation applies to a given contract.
    Returns a FormalisationBoundary because the renewal exemption gating
    condition ("material change") is a Discretionary determination.

    The honest result for a renewal contract is `boundary` — the provider
    must self-assess materiality, subject to ACCC oversight.
    For non-renewal contracts, the obligation is formally established. -/
def assessCISCompliance
    (c : ServiceContract) (cis : Option CIS)
    : FormalisationBoundary Prop :=
  if !c.consumer.isIndividual then
    -- Not a consumer contract: TCP 5.1 does not apply
    FormalisationBoundary.formal False
  else if c.isRenewal then
    -- Renewal: exemption MAY apply, but depends on material change (Discretionary)
    FormalisationBoundary.boundary
      ("Renewal contract: CIS exemption (TCP 5.1.3) applies only if there is no " ++
       "material change to terms. 'Material change' is a discretionary determination.")
      "Provider (initial determination) + ACCC (review)"
  else
    -- Non-renewal: CIS is obligatory; check if one was actually provided
    match cis with
    | none =>
        -- No CIS provided: formally non-compliant
        FormalisationBoundary.formal False
    | some s =>
        if s.isStandardFormat && s.pageCount ≤ 2 then
          -- Compliant CIS provided before commitment: formally satisfied
          FormalisationBoundary.mixed
            ("CIS provided in standard ACCC format within " ++
             Nat.repr s.pageCount ++ " pages — structurally compliant")
            ("Whether CIS was provided 'before the consumer became committed' " ++
             "requires determination of the exact commitment moment (TCP 5.1.2)")
        else
          -- CIS fails format or page-count requirement: formally non-compliant
          FormalisationBoundary.formal False

/-- Determine whether a specific ETF is compliant with TCP 8.2.
    Returns a FormalisationBoundary because "direct costs" is a Vague term
    requiring ACCC/TIO/court determination.

    Formally verified: device repayment carve-out applies or does not.
    Boundary: whether the fee amount exceeds "direct costs" (IsWithinDirectCosts). -/
def assessETFCompliance (etf : ETF) : FormalisationBoundary Prop :=
  if etf.isDeviceRepayment then
    -- D3 applies: device repayment carve-out defeats the prohibition
    FormalisationBoundary.boundary
      ("Device repayment carve-out (TCP 8.2.4) applies — fee relates to " ++
       "outstanding handset/device repayment under a device payment plan. " ++
       "Whether the amount correctly reflects outstanding repayment requires verification.")
      "ACCC / TIO (on consumer complaint)"
  else
    -- General prohibition applies: "direct costs" cap is open-texture
    FormalisationBoundary.boundary
      ("TCP 8.2 applies: ETF must not exceed direct costs of early termination. " ++
       "Whether the fee amount is within 'direct costs' is a Vague determination " ++
       "(ACCC v Telstra (2016)): network provisioning costs included; " ++
       "customer acquisition costs and lost profit excluded.")
      "ACCC / TIO / courts"

-- ============================================================
-- Governatori DDL comparison: encoding the same rules in DDL
-- (documented as comments — the canonical DDL encoding)
-- ============================================================

/-
  The three TCP Code rules above in Governatori's Defeasible Deontic Logic:

    -- R1: Contact obligation (defeasible)
    d ⊗ (isLicensed(P)) ⇒ O(publishContactDetails(P))
    r1 :- licensed(P), not small_provider(P).        -- defeasible antecedent
    O(publishContactDetails(P)) :- r1.               -- deontic consequence

    -- D1: Small provider exception (defeats R1)
    r1_exc :- small_provider(P).
    r1_exc > r1                                       -- priority declaration

    -- R2: CIS obligation
    d ⊗ (isConsumerContract(C)) ⇒ O(provideCIS(C))
    r2 :- consumer_contract(C), not renewal_exempt(C).
    r2_exc :- renewal(C), not material_change(C).
    r2_exc > r2

    -- R3: ETF prohibition
    d ⊗ (isFixedTerm(C)) ⇒ F(chargeExcessiveETF(C))
    r3 :- fixed_term(C), not device_repayment(C).
    r3_exc :- device_repayment(C).
    r3_exc > r3

  What DDL cannot express that LegalLean can:
    1. FormalisationBoundary: DDL treats `prominently_published(P)`,
       `within_reasonable_time(P)`, and `material_change(C)` as ordinary atoms.
       LegalLean's Vague/Discretionary instances make the open-texture character
       of these conditions MACHINE-READABLE and auditable.
    2. Dependent types: `LegalRule (α : Type)` parameterises the rule by the
       type of entity it governs. DDL has no such type-level structure — all
       rules share a flat first-order signature.
    3. Evidence witnesses: `EvidenceFor P` requires a term-level proof. DDL
       can express that a rule's conclusion "holds" but cannot require a
       constructive witness (proof term) for that holding.
    4. Cardinality constraints: (used in O1Visa) `AllDistinct` + `List.length ≥ N`
       is expressible in Lean 4 types; DDL has no such built-in.
-/

-- ============================================================
-- Theorems: machine-verified properties of the TCP Code kernel
-- ============================================================

/-- Theorem T1: R1 (contact obligation) and R1_SmallProviderExemption have
    distinct deontic modalities.
    R1 is obligatory (providers MUST publish contact details);
    R1_SmallProviderExemption is permitted (small providers MAY use simplified requirements).
    This deontic asymmetry [different normative force] is legally significant:
    the exemption is a permission, not a counter-obligation. -/
theorem contact_obligation_and_exemption_are_deontic_distinct :
    R1_ContactObligation.modality ≠ R1_SmallProviderExemption.modality := by
  simp [R1_ContactObligation, R1_SmallProviderExemption]

/-- Theorem T2: R3 (ETF prohibition) and R3_DeviceRepaymentCarveout have
    distinct deontic modalities.
    R3 is prohibited (providers MUST NOT charge excessive ETFs);
    R3_DeviceRepaymentCarveout is permitted (device repayment fees ARE allowed).
    Formally proves the carve-out is a permission that suspends the prohibition,
    not a separate prohibition. -/
theorem etf_prohibition_and_carveout_are_deontic_distinct :
    R3_ExcessiveETFProhibited.modality ≠ R3_DeviceRepaymentCarveout.modality := by
  simp [R3_ExcessiveETFProhibited, R3_DeviceRepaymentCarveout]

/-- Theorem T3: The defeat graph is acyclic [no rule defeats itself].
    Each defeat relation satisfies defeater ≠ defeated.
    Acyclicity is a necessary soundness condition for any defeasible system:
    if a rule defeated itself, it would simultaneously establish and retract
    its own conclusion — logical inconsistency. -/
theorem defeat_graph_acyclic :
    ∀ d ∈ allDefeats, d.defeater ≠ d.defeated := by
  intro d hd
  simp [allDefeats] at hd
  rcases hd with rfl | rfl | rfl
  · simp [defeat_D1_SmallProviderExemption_ContactObligation]
  · simp [defeat_D2_RenewalExemption_CriticalInfoSummary]
  · simp [defeat_D3_DeviceRepaymentCarveout_ETFProhibited]

/-- Theorem T4: assessContactCompliance returns `formal False` for unlicensed providers.
    If a provider is not licensed, the TCP Code does not apply to them.
    This is a pure formal result — no open texture involved.
    Demonstrates that the type checker can enforce the scope of the regulatory code. -/
theorem unlicensed_provider_not_subject_to_tcp
    (p : Provider) (cd : ContactDetails)
    (h : p.isLicensed = false)
    : assessContactCompliance p cd = FormalisationBoundary.formal False := by
  simp [assessContactCompliance, h]

/-- Theorem T5: A non-individual consumer contract is outside TCP 5.1 scope.
    assessCISCompliance returns `formal False` if the consumer is not an individual.
    The CIS obligation is scoped to retail consumers only (personal/domestic use).
    Pure formal result — demonstrates compositional correctness of the scoping logic. -/
theorem non_consumer_contract_outside_cis_scope
    (c : ServiceContract) (cis : Option CIS)
    (h : c.consumer.isIndividual = false)
    : assessCISCompliance c cis = FormalisationBoundary.formal False := by
  simp [assessCISCompliance, h]

/-- Theorem T6: assessCISCompliance for non-renewal contracts with a non-standard-format
    CIS returns `formal False`.
    Proves that a CIS that fails the format requirement is formally non-compliant
    regardless of open-texture conditions — there is no ambiguity here.
    (The isStandardFormat field is a formalisable Bool condition.) -/
theorem non_compliant_cis_format_is_formal_failure
    (c : ServiceContract) (s : CIS)
    (h_individual : c.consumer.isIndividual = true)
    (h_not_renewal : c.isRenewal = false)
    (h_format : s.isStandardFormat = false)
    : assessCISCompliance c (some s) = FormalisationBoundary.formal False := by
  simp [assessCISCompliance, h_individual, h_not_renewal, h_format]

/-- Theorem T7: Defeat priorities are well-ordered — the exemption rules have
    strictly higher priority levels than the rules they defeat.
    This is a structural soundness property: in any correctly designed defeasible
    system, the defeating rule must outrank the rule it defeats. -/
theorem exemption_rules_outrank_base_rules :
    R1_SmallProviderExemption.priority.level > R1_ContactObligation.priority.level ∧
    R2_RenewalExemption.priority.level > R2_CriticalInfoSummary.priority.level ∧
    R3_DeviceRepaymentCarveout.priority.level > R3_ExcessiveETFProhibited.priority.level := by
  simp [R1_SmallProviderExemption, R1_ContactObligation,
        R2_RenewalExemption, R2_CriticalInfoSummary,
        R3_DeviceRepaymentCarveout, R3_ExcessiveETFProhibited]

-- ============================================================
-- HEADLINE THEOREMS (equivalent depth to IRC163h)
-- ============================================================

/-- Theorem T8: A licensed small provider cannot be simultaneously
    subject to the full contact obligation AND the exemption.
    The exemption DEFEATS the obligation — the two cannot both be
    "active" for the same provider simultaneously.

    Proved by showing that when `isSmallProvider p` holds, `assessContactCompliance`
    returns `boundary` (the exemption path), NOT `mixed` (the full-obligation path).
    Since the two constructors are distinct, a single call cannot return both.

    Legal significance: the defeat relation is not merely a priority tie-breaker;
    it is an exclusion — once the exemption condition is met, the obligation's
    full machinery does NOT apply. This is lex specialis [more specific rule
    overrides the general one] as a logical exclusion, not just a tie-break.

    Note: we also require `isLicensedProvider p` because unlicensed providers
    are in scope of a third, distinct branch (`formal False`). The theorem is
    specifically about the obligation-vs-exemption conflict for licensed providers. -/
theorem small_provider_exemption_defeats_obligation
    (p : Provider) (cd : ContactDetails)
    (h_licensed : p.isLicensed = true)
    (h_small : p.employeeCount < 10)
    : ∃ r auth,
        assessContactCompliance p cd =
          FormalisationBoundary.boundary r auth := by
  simp [assessContactCompliance, h_licensed, h_small]

/-- Corollary: A licensed small provider's contact assessment is NOT `mixed`.
    The `mixed` result represents the FULL obligation path (structural check
    passed, prominence still requires ACCC). The `boundary` result represents
    the exemption path. These are mutually exclusive outcomes — the two
    normative regimes (obligation vs exemption) cannot coexist in a single
    compliance determination. -/
theorem small_provider_not_in_obligation_path
    (p : Provider) (cd : ContactDetails)
    (h_licensed : p.isLicensed = true)
    (h_small : p.employeeCount < 10)
    : ∀ fp hp,
        assessContactCompliance p cd ≠
          FormalisationBoundary.mixed fp hp := by
  simp [assessContactCompliance, h_licensed, h_small]

/-- Theorem T9: All three compliance assessment functions return `boundary`
    when the relevant exemption condition is active.
    This proves structural uniformity across the three TCP Code provisions:
    in every case where a lex specialis exemption fires, the outcome is
    `boundary` (requires authority determination), not `formal` or `mixed`.

    - assessContactCompliance: small provider → boundary
    - assessCISCompliance:     renewal contract → boundary
    - assessETFCompliance:     device repayment → boundary

    Why this matters: DDL would encode these as defeasible atoms with no
    distinction between "machine-decided" and "authority-decided" outcomes.
    LegalLean proves that the exemption paths consistently route to the same
    `FormalisationBoundary` constructor — a structural invariant [property
    that holds across all cases] that DDL cannot express or verify. -/
theorem all_exemptions_yield_boundary
    -- (i) Contact: licensed small provider → boundary
    (p : Provider) (cd : ContactDetails)
    (h_lic : p.isLicensed = true) (h_small : p.employeeCount < 10)
    -- (ii) CIS: individual renewal → boundary
    (c : ServiceContract) (cis : Option CIS)
    (h_ind : c.consumer.isIndividual = true) (h_renew : c.isRenewal = true)
    -- (iii) ETF: device repayment → boundary
    (etf : ETF) (h_dev : etf.isDeviceRepayment = true)
    : (∃ r1 a1, assessContactCompliance p cd = FormalisationBoundary.boundary r1 a1) ∧
      (∃ r2 a2, assessCISCompliance c cis = FormalisationBoundary.boundary r2 a2) ∧
      (∃ r3 a3, assessETFCompliance etf = FormalisationBoundary.boundary r3 a3) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [assessContactCompliance, h_lic, h_small]
  · simp [assessCISCompliance, h_ind, h_renew]
  · simp [assessETFCompliance, h_dev]

/-- Theorem T10: All three defeat relations are STRICT.
    A strict defeat [d.strict = true] means the exemption ALWAYS wins —
    there is no further rule that can re-defeat the exemption itself.
    In contrast, non-strict defeat can itself be defeated (rebuttable).

    This proves the TCP Code's exemption hierarchy is completely determined
    at rule-definition time: there is no "meta-rule" that can override the
    small provider exemption, the renewal exemption, or the device carve-out.

    This is a stronger claim than T7 (which only proves priority ordering):
    strict defeat means the outcome is deterministic once the exemption fires,
    whereas a non-strict defeat could still be overridden by a higher rule. -/
theorem all_defeats_are_strict :
    ∀ d ∈ allDefeats, d.strict = true := by
  intro d hd
  simp [allDefeats] at hd
  rcases hd with rfl | rfl | rfl
  · simp [defeat_D1_SmallProviderExemption_ContactObligation]
  · simp [defeat_D2_RenewalExemption_CriticalInfoSummary]
  · simp [defeat_D3_DeviceRepaymentCarveout_ETFProhibited]

/-- Theorem T11: The defeat hierarchy is consistent — every defeater has
    strictly higher priority than the rule it defeats.
    This is the formal proof that lex specialis [more specific rule overrides
    general] is encoded correctly: not just by convention but by a verifiable
    numeric priority ordering.

    Combines T7's priority ordering with T3's acyclicity to establish a
    well-founded [no infinite descending chains] defeat relation. -/
theorem defeat_hierarchy_is_consistent :
    ∀ d ∈ allDefeats, d.strict = true ∧ d.defeater ≠ d.defeated := by
  intro d hd
  constructor
  · exact all_defeats_are_strict d hd
  · exact defeat_graph_acyclic d hd

end LegalLean.CaseStudies.TCPCode
```

## File: monograph/verified-legal-reasoning.md

```lean
# Verified Legal Reasoning: From Natural Language to Formal Proof

**Eduardo Aguilar Pelaez**
Legal Engine Ltd, London, UK / Imperial College London, UK
edu@legalengine.co.uk | e.aguilar@imperial.ac.uk

---

## Abstract

Legal AI systems increasingly serve as transducers -- converting unstructured statutory text into structured representations -- but they lack a verification layer capable of distinguishing what the type checker can certify from what requires human judgment. This paper presents LegalLean, a framework for verified legal reasoning built on Lean 4 dependent types. The central contribution is the `FormalisationBoundary` type and the `RequiresHumanDetermination` typeclass, which together encode Hart's "open texture" distinction as a first-class object in the type system rather than an external limitation on formalisation. We demonstrate the framework across three case studies: IRC §163(h) mortgage interest deduction, the O-1A extraordinary ability visa (8 CFR §204.5(h)), and the Australian Telecommunications Consumer Protections Code (C622:2012). The system produces 44 machine-verified theorems with zero unresolved `sorry` placeholders. The headline result is `monotonicity_break_general`: a machine-checked proof that the Tax Cuts and Jobs Act 2017 removed a previously valid deduction permission for all home equity interest payments -- a formally verified instance of non-monotonic statutory change. We compare LegalLean against four prior systems (DDL, Catala, L4L, LegalRuleML) and discuss honest limitations.

---

## 1. Introduction

Google DeepMind's description of its language model as a "transducer and verifier" articulates a productive division of labour: the language model converts messy natural-language input into structured form, while a separate verification layer checks the logic. This framing, applied to law, identifies exactly what is missing from current legal AI systems. Systems that extract rules from statutes, answer legal queries, or assess compliance are, in this terminology, transducers. They produce structured representations. None of them includes a verifier in the formal sense: a component that provides machine-checkable guarantees about the reasoning it performs.

The gap matters because legal reasoning has a well-understood failure mode. Hart's analysis in *The Concept of Law* [11] identified that legal concepts have a core of settled meaning and a penumbra of uncertainty. A formalisation that does not distinguish these zones does not merely lack nuance -- it silently misrepresents where its own confidence ends. When a compliance system returns "non-compliant", the user cannot tell whether that verdict rests on a formally verifiable ground (the payment was not made by an individual) or a contestable judgment (the property may not qualify as a "qualified residence"). Both appear as outputs; only one is machine-checkable.

Existing approaches address parts of this problem but not the whole. Catala [14] is a functional programming language designed for statutes: it computes legal outcomes deterministically but has no mechanism for representing open texture -- the code either handles a case or raises a runtime error. Governatori's Defeasible Deontic Logic (DDL) [9, 10] encodes legal rules as defeasible clauses with priority relations, handling non-monotonicity well but providing no machine-checkable proofs and treating vague predicates as ordinary literals. L4L (Logic for Law) [12] uses dependent types in a style close to ours and produces SMT-backed proofs, but the SMT layer is not fully transparent: the proof obligations are discharged by a solver whose output is not an auditable term. LegalRuleML [16] is a rich XML vocabulary for regulatory knowledge but provides no automated reasoning whatsoever. None of these systems makes the formalisation boundary itself a typed, auditable object.

LegalLean takes a different approach. It uses Lean 4 [7] dependent types, where the Curry-Howard correspondence [5, 6] establishes that propositions are types and proofs are terms. A legal conclusion -- "this interest payment is not deductible" -- is a type. A proof of that conclusion is a term of that type. If the term type-checks, the conclusion is verified; if it does not, the error is explicit and localised. Crucially, when a legal condition requires human determination (because the underlying predicate is vague or discretionary), LegalLean does not attempt to discharge it. Instead, it wraps the proposition in a `FormalisationBoundary` value that carries machine-readable metadata about which institution must determine it and why.

The contributions of this paper are:

1. The `FormalisationBoundary` inductive type and the `RequiresHumanDetermination` typeclass (with `Vague` and `Discretionary` subclasses), providing the first formal treatment of Hart's open texture as a machine-checkable type-level distinction.

2. A verified encoding of IRC §163(h) including `monotonicity_break_general`, a machine-checked proof that the TCJA 2017 constitutes a non-monotonic statutory change: for every home equity payment satisfying the pre-TCJA conditions, the legal outcome transitions from `boundary` (human determination required) to `formal False` (machine-verified rejection).

3. A dependent-type encoding of the O-1A visa "3 of 8" threshold using `AllDistinct` lists with length constraints, together with a `mixed` formalisation of the Kazarian two-part test.

4. A structured comparison of LegalLean against DDL [9], Catala [14], L4L [12], and LegalRuleML [16] across seven dimensions.

All source code is available and compiles against Lean 4 v4.24.0 (the Aristotle release) with no Mathlib dependency.

---

## 2. Background

### 2.1 Hart's Open Texture

In *The Concept of Law* (1961), H.L.A. Hart [11] observed that legal concepts have a "core of settled meaning" and a "penumbra of uncertainty". The canonical example is a rule prohibiting vehicles in a park: a car is unambiguously within the rule's core; a toy pedal car is in the penumbra. The penumbral question cannot be resolved by logic alone -- it requires a judgment about the rule's purpose and the case's particulars. Hart called this irreducible property "open texture": the meaning of legal terms cannot be fully determined in advance, and no formalisation can eliminate the need for human judgment at the boundary.

Prior legal knowledge representation systems treat open texture as a limitation imposed from outside: the formalisation goes as far as it can, and the rest is left to the practitioner. LegalLean treats it as a property to be represented inside the system.

### 2.2 Default Logic and Defeasibility

Legal reasoning is non-monotonic [defeasible]: adding new rules or evidence can retract previously valid conclusions. Lawsky's "A Logic for Statutes" [13] provides a careful analysis of how Reiter's default logic [17] applies to statutory interpretation, demonstrating that statutes encode default rules of the form: "if conditions hold and no exception applies, the conclusion follows." The exceptions are themselves defeasible, creating chains of defeat.

LegalLean represents defeasibility through the `Defeats` structure and `DefeasiblyHolds` proposition type. Priority ordering (lex posterior, lex specialis) is encoded in the `Priority` field of each `LegalRule`. The key departure from prior work is that defeat relations are typed: the `Defeats` structure carries a `reason` field distinguishing lex posterior from lex specialis, and its `strict` field distinguishes hard from soft defeat.

### 2.3 Curry-Howard and Lean 4

The Curry-Howard correspondence [5, 6] establishes an isomorphism between propositions and types: a proposition `P` is inhabited (has a term of that type) if and only if it is provable. In Lean 4 [7], this means that constructing a value of type `EvidenceFor P` is literally the same operation as proving `P`. Lean 4's kernel verifier checks all proof terms, making the guarantee machine-checkable in a stronger sense than SMT: the checker is a small, auditable kernel, not an opaque solver.

Lean 4's dependent type system allows the type of a term to depend on its value. This is essential for legal formalisation: the type of evidence required for "meets 3 of 8 criteria" depends on which specific criteria are claimed, and `MeetsThreeCriteria` encodes this directly via an `AllDistinct` list of `Criterion` values with a `cardinal` proof that `satisfied.length >= 3`.

---

## 3. The LegalLean Framework

### 3.1 Core Types

The framework begins with three foundational types defined in `LegalLean.Core`:

```lean
inductive Deontic where
  | permitted    : Deontic
  | prohibited   : Deontic
  | obligatory   : Deontic
  deriving Repr, BEq, Inhabited, DecidableEq
```

The deontic modalities cover the three fundamental normative positions. Lean 4's `DecidableEq` derivation means that equality of modalities is decidable, enabling automated conflict detection in theorems (for instance, `R1_BaseDeduction.modality ≠ R2_TCJAProhibition.modality` is proved by `simp`).

```lean
structure LegalRule (α : Type) where
  id          : String
  description : String
  modality    : Deontic
  priority    : Priority
  conclusion  : α → Prop
  defeatedBy  : List String
```

`LegalRule` is parameterised by the type `α` of the entity it governs: `LegalRule InterestPayment` for IRC §163(h) rules, `LegalRule Provider` for TCP Code rules. The `conclusion` field is a function from `α` to `Prop`, encoding the rule's conclusion as a dependent proposition. This is more expressive than DDL's flat first-order signature.

```lean
structure EvidenceFor (P : Prop) where
  source   : String
  artifact : Option String
  witness  : P
```

`EvidenceFor P` is the propositions-as-types materialisation of legal evidence: the `witness` field literally contains the proof of `P`. Constructing an `EvidenceFor P` value is constructing a proof. The `source` and `artifact` fields provide provenance that survives code evolution -- they are not erased at compile time.

### 3.2 The FormalisationBoundary Type

`FormalisationBoundary` is the novel contribution of this framework:

```lean
inductive FormalisationBoundary (P : Sort _) where
  | formal   (proof : P)                                  : FormalisationBoundary P
  | boundary (reason : String) (authority : String)       : FormalisationBoundary P
  | mixed    (formalPart : String) (humanPart : String)   : FormalisationBoundary P
```

The three constructors correspond to three epistemic positions about a legal proposition `P`:

- `formal proof`: the type checker alone can verify `P`. No human determination is required. The `proof` term is a machine-checked certificate.
- `boundary reason authority`: `P` requires human determination. The `reason` string names the specific open-texture condition; `authority` names the institution responsible.
- `mixed formalPart humanPart`: `P` is partially formal and partially boundary. Part 1 of the Kazarian two-part test is `formal` (Lean verified the criteria count); Part 2 is `boundary` (USCIS holistic determination).

### 3.3 The RequiresHumanDetermination Typeclass

The `FormalisationBoundary` type marks where the boundary falls. The `RequiresHumanDetermination` typeclass marks which propositions are intrinsically at the boundary:

```lean
class RequiresHumanDetermination (P : Prop) where
  reason    : String
  authority : String

class Vague (P : Prop) extends RequiresHumanDetermination P where
  core      : String
  penumbra  : String

class Discretionary (P : Prop) extends RequiresHumanDetermination P where
  scope       : String
  constraints : List String
```

`Vague` captures Hart's core/penumbra distinction directly. `core` describes settled cases; `penumbra` describes the contested region. `Discretionary` captures a different phenomenon: not conceptual vagueness but institutional authority. A USCIS adjudicator's determination of "extraordinary ability" is not vague in Hart's sense -- the adjudicator has the power to decide. The typeclass distinguishes these two sources of non-formalisability.

Both typeclasses constrain proof search: any proposition with a `Vague` or `Discretionary` instance cannot be discharged by the type checker without an explicit axiom. In the case studies, open-texture propositions such as `HasExtraordinaryAbility` and `IsQualifiedResidence` are introduced as axioms -- honest markers that the type checker cannot verify them. The typeclass instances then carry the auditable metadata explaining why.

The use of axioms for open-texture propositions requires justification. An axiom in Lean 4 is a proposition asserted without proof; it is not verified by the kernel. One might object that this introduces a soundness gap: if the axioms are inconsistent, any theorem built on them is vacuously true. This objection is correct in principle but misdirected in practice. The axioms are not intended to be discharged; they represent propositions that *should not* be machine-verifiable. A system that could prove `HasExtraordinaryAbility a` for a given applicant `a` would be claiming to have automated a determination that the US Congress assigned to USCIS adjudicators. The axiom marks the boundary between what the type checker should certify and what it should defer. The theorems built on these axioms do not depend on their truth -- they depend on their *structure*. The monotonicity break theorem, for instance, does not use any open-texture axiom; it reasons entirely about the formalisable conditions.

This is the key architectural difference from all prior systems: the formalisation boundary is not a gap in the encoding but a typed, first-class object.

---

## 4. Case Studies

### 4.1 IRC §163(h): Mortgage Interest Deduction

IRC §163(h) (26 U.S.C. §163(h)) is the provision of the US Internal Revenue Code governing the deductibility of qualified residence interest. It was chosen because Lawsky [13] used it as the gold standard case study for default logic applied to statutes. The rule structure, discovered and verified through the research pipeline, consists of three rules, four defeat relations forming a three-level chain, and three open-texture terms.

The three rules in `LegalLean.CaseStudies.IRC163h` are:

- **R1** (`R1_BaseDeduction`): Taxpayers are permitted to deduct interest on acquisition indebtedness secured by a qualified residence. Priority level 1 ("statute").
- **R2** (`R2_TCJAProhibition`): Home equity interest deduction is prohibited for taxable years beginning after 15 December 2017 (the TCJA). Priority level 2 ("statute (TCJA 2017, lex posterior)").
- **R3** (`R3_GrandfatherRule`): Acquisition indebtedness outstanding on 13 October 1987 is grandfathered from current dollar limits. Priority level 3 ("statute (lex specialis, grandfather clause)").

The four defeat relations are: R2 defeats R1 (lex posterior); E1.1 (dollar limit) defeats R1; E1.2 (home equity dollar limit) defeats R1; and R3 defeats E1.1. The third of these creates a three-level defeasibility chain: R3 defeats E1.1, which defeats R1 -- defeat of the limit restores the base permission. This chain cannot be represented by a flat priority ordering; it requires the full defeasibility machinery.

Open-texture terms are encoded as axioms with `Vague` instances. `IsQualifiedResidence` is declared as an axiom, with the instance documenting the core (principal residence plus one other property used as a residence) and the penumbra (mobile homes, timeshares, boats with habitability facilities, fractional ownership). `IsSubstantialImprovement` receives the same treatment. `MixedUseAllocation` receives a `Discretionary` instance referencing IRS tracing rules under Treas. Reg. §1.163-8T.

The compliance function `isDeductible` returns a `FormalisationBoundary Prop`. For unlicensed entities, post-TCJA home equity, and unsecured debt, it returns `formal False` -- machine-verified rejection. For acquisition indebtedness within limits, it returns `boundary` with the authority "IRS / Tax Court".

#### 4.1.1 The Monotonicity Break Theorem

The headline result of this case study is `monotonicity_break_general`:

```lean
theorem monotonicity_break_general
    (payment : InterestPayment) (status : FilingStatus)
    (h_individual : payment.paidByIndividual = true)
    (h_secured    : payment.indebtedness.securedByResidence = true)
    (h_purpose    : payment.indebtedness.purpose = IndebtednessPurpose.other)
    (h_within     : withinHomeEquityLimit payment.indebtedness status = true)
    : (∃ r a, isDeductible payment ⟨2017⟩ status =
                FormalisationBoundary.boundary r a) ∧
      (isDeductible payment ⟨2018⟩ status =
                FormalisationBoundary.formal False) := by
  constructor
  · simp [isDeductible, h_individual, h_secured, h_purpose, h_within]
  · simp [isDeductible, h_individual, h_secured, h_purpose]
```

This theorem states, for all home equity interest payments by individual taxpayers on secured property within the applicable dollar limits: the pre-TCJA outcome (year = 2017) is `boundary` (potentially deductible; human determination of "qualified residence" required), while the post-TCJA outcome (year = 2018) is `formal False` (automatically rejected; machine-verified). The TCJA added a rule to the legal system that removed a previously available permission. Lean 4 verifies this as a structural property of the encoding, not merely a test case.

A companion corollary `pre_tcja_not_auto_rejected` confirms the strictness of the break: the pre-TCJA outcome is provably not `formal False`, making the transition genuinely from "possibly permitted" to "certainly prohibited."

It is worth being explicit about what this theorem proves and does not prove. It proves a structural property of the formalisation: that the `isDeductible` function, as encoded, produces these two outcomes for these two inputs. It does not prove that the formalisation is a complete representation of IRC §163(h) -- such a claim would require independent legal audit. The theorem's value is that it is machine-checked: the outcome cannot diverge silently from the encoding.

A natural question is whether the proof's brevity (two `simp` calls) indicates that the result is trivially encoded. It does not. The `simp` tactic unfolds `isDeductible`, substitutes the hypotheses, and evaluates the `if` branches. The non-triviality is in the *universality*: the theorem quantifies over all `InterestPayment` values and all `FilingStatus` values satisfying the four preconditions. A test case checks one input; this theorem checks the entire input space. The preconditions are exactly the conditions under which the monotonicity break is legally relevant (individual taxpayer, secured home equity debt within limits), and the universally quantified conclusion is that the legal outcome changes at the 2018 boundary for every such payment. This structural coverage is what distinguishes a verified theorem from a unit test, even when both share the same tactic.

### 4.2 O-1A Visa: "3 of 8" as Dependent Types

The O-1A extraordinary ability visa (8 CFR §204.5(h)) requires demonstrating "extraordinary ability" by meeting at least three of eight evidentiary criteria. This is a natural dependent-type problem: the "3 of 8" threshold is a cardinality constraint on a set of satisfied criteria, and Lean 4 can encode this constraint at the type level.

The eight criteria are defined as an inductive type `Criterion` with `DecidableEq`, allowing duplicate-free lists. Since the case study avoids Mathlib, cardinality is encoded without `Finset`:

```lean
inductive AllDistinct {α : Type} [DecidableEq α] : List α → Prop
  | nil  : AllDistinct []
  | cons : ∀ {x : α} {xs : List α}, x ∉ xs → AllDistinct xs
               → AllDistinct (x :: xs)

structure MeetsThreeCriteria (a : Applicant) where
  satisfied : List Criterion
  distinct  : AllDistinct satisfied
  cardinal  : satisfied.length ≥ 3
  evidence  : ∀ c ∈ satisfied, LegalLean.EvidenceFor (criterionProp a c)
```

A value of type `MeetsThreeCriteria a` can only be constructed if one provides a duplicate-free list of at least three criteria together with `EvidenceFor` witnesses for each. The type checker enforces the threshold at compile time. This is precisely the propositions-as-types reading of "the applicant meets the threshold": inhabiting the type is proving the claim.

The `criterionProp` function maps each `Criterion` to a `Prop`. Most criteria are mapped to `HasExtraordinaryAbility`, which is declared as an axiom with a `Vague` instance documenting the core (Nobel laureates, Olympic medallists, field-leading researchers with major international awards) and the penumbra (the boundary between "very accomplished" and "extraordinary"; field-relative standards; weight given to each criterion in combination). The `highSalary` criterion is mapped to `SalaryIsHigh`, which has its own `Vague` instance, and `originalContribs` to `ContributionsAreMajor` with a `Discretionary` instance.

The Kazarian two-part test (Kazarian v. USCIS, 596 F.3d 1115, 9th Cir. 2010) is encoded by `determineEligibility`, which returns `FormalisationBoundary.mixed`: the `formalPart` records that Lean verified the criteria count; the `humanPart` names the USCIS adjudicator and the final merits determination as the non-formalisable component. The theorem `eligibility_always_mixed` proves that `determineEligibility` always returns `mixed` -- never `formal` or `boundary` alone -- which is a structural consequence of the Kazarian framework: Part 1 is always machine-checkable; Part 2 is always not.

The `ComparableEvidenceApplies` axiom (8 CFR §204.5(h)(4)) receives a `Discretionary` instance with two constraints: the adjudicator must determine both that standard criteria do not apply to the field and that the comparable evidence meets the same substantive threshold (Rijal v. USCIS).

### 4.3 TCP Code: Deontic Spectrum and DDL Comparison

The third case study encodes a kernel of the Australian Telecommunications Consumer Protections Code (C622:2012), chosen for direct comparison with Governatori's DDL encoding of the same regulatory text [9, 10]. Three provisions are encoded: TCP 3.2 (contact details obligation), TCP 5.1 (Critical Information Summary obligation), and TCP 8.2 (excessive early termination fee prohibition). Each has a lex specialis defeat: small provider exemption, renewal exemption, and device repayment carve-out respectively.

The three provisions demonstrate the full deontic spectrum: TCP 3.2 imposes an obligation (providers must publish contact details); TCP 8.2 imposes a prohibition (providers must not charge excessive ETFs); and the defeat rules introduce permissions (small providers may use simplified requirements; device repayment fees are allowed). The theorems `contact_obligation_and_exemption_are_deontic_distinct` and `etf_prohibition_and_carveout_are_deontic_distinct` prove that the base rule and its defeating exception always have distinct modalities -- the exception is a permission that suspends an obligation or prohibition, not a counter-obligation.

The `exemption_rules_outrank_base_rules` theorem verifies that defeating rules have strictly higher priority levels than the rules they defeat across all three provisions:

```lean
theorem exemption_rules_outrank_base_rules :
    R1_SmallProviderExemption.priority.level > R1_ContactObligation.priority.level ∧
    R2_RenewalExemption.priority.level > R2_CriticalInfoSummary.priority.level ∧
    R3_DeviceRepaymentCarveout.priority.level > R3_ExcessiveETFProhibited.priority.level
```

This is a structural soundness property: a defeat relation where the defeating rule had lower or equal priority would be incoherent.

The DDL encoding of the same provisions is documented as comments in the source file. For example, the contact obligation in DDL syntax:

```
d ⊗ (isLicensed(P)) ⇒ O(publishContactDetails(P))
r1 :- licensed(P), not small_provider(P).
r1_exc :- small_provider(P).
r1_exc > r1
```

The LegalLean encoding differs in four respects: (1) `FormalisationBoundary` distinguishes `prominently_published` from `is_licensed` as requiring human determination, rather than treating both as ordinary literals; (2) `LegalRule (α : Type)` parameterises rules by the entity type, producing a typed rather than flat signature; (3) `EvidenceFor P` requires a proof witness rather than mere assertion; (4) the `Vague` and `Discretionary` instances carry auditable metadata that is machine-readable, not just a comment.

---

## 5. Evaluation

### 5.1 Theorem Count and Properties

The system produces 44 machine-verified theorems with zero `sorry` placeholders across the three case studies. It is important to be honest about the nature of these theorems. Some are structural unit tests: `non_individual_never_deducts` is proved by `simp [isDeductible, h]` -- a trivial path trace through a function. These theorems are valuable as regression tests but do not constitute substantive contributions in isolation.

Others are more substantive. `monotonicity_break_general` requires reasoning about two distinct legal regimes and proving a structural divergence. `defeat_chain_exists` proves that the defeat relation in IRC §163(h) has genuine depth -- R3 defeats E1.1, which defeats R1, but R3 does not directly defeat R1 -- capturing a legally meaningful subtlety about the grandfather clause. `no_mixed_outcomes` proves by full case analysis that IRC §163(h)'s `isDeductible` function never returns a `mixed` result, establishing a binary structure (either fully formal or requires human determination) as a property of the statute rather than a design choice.

A faithfulness audit identified three areas where the encoding simplifies the actual law: (1) date comparisons use ISO 8601 string ordering rather than proper date arithmetic; (2) `criterionProp` maps multiple distinct O-1A criteria to the same axiom (`HasExtraordinaryAbility`) for pragmatic reasons, losing some per-criterion resolution; (3) the IRC §163(h) encoding does not handle the full debt tracing rules of Treas. Reg. §1.163-8T, which require temporal tracking of how loan proceeds were used.

### 5.2 Comparison with Prior Systems

The following table compares LegalLean against four prior systems across seven dimensions. Scores are on a 1--5 scale. As noted below, these scores should be treated with caution.

| Dimension | LegalLean | L4L | DDL | Catala | LegalRuleML |
|-----------|-----------|-----|-----|--------|-------------|
| Compositional semantics | 5 | 3 | 4 | 4 | 2 |
| Deontic modalities | 5 | 4 | 5 | 2 | 4 |
| Dependent types (evidence-as-inhabitants) | 5 | 5 | 1 | 1 | 1 |
| Machine-checkable guarantees | 5 | 3 | 3 | 4 | 1 |
| Open texture encoding | 5 | 3 | 4 | 2 | 2 |
| Provenance tracking | 5 | 5 | 4 | 3 | 4 |
| Temporal reasoning | 5 | 3 | 4 | 3 | 4 |
| **Total** | **35** | **26** | **25** | **19** | **18** |

These scores were generated as part of a structured comparison exercise and must be interpreted with appropriate scepticism. The scores for LegalLean are perfect (5/5 on every dimension), which reflects the dimensions being chosen partly to highlight LegalLean's strengths. A reviewer who weighted, for example, practical adoption, tool maturity, or non-expert usability would produce different rankings. The scores should be read as indicating the dimensions on which LegalLean makes a genuine claim, not as an objective ranking.

**DDL** [9, 10] (Governatori): strong on deontic modalities and temporal reasoning; the most mature industrial-strength defeasible logic system for law. Its limitation for LegalLean's purposes is that it treats all conditions as first-order literals -- `prominently_published(P)` is no different from `is_licensed(P)` in the DDL signature. There is no mechanism to mark the former as requiring institutional determination and the latter as a formal Boolean check.

**Catala** [14] (Merigoux et al.): designed specifically for tax and social benefit statutes, with excellent practical coverage. It computes legal outcomes rather than proving properties about them: Catala programs execute, they do not produce proof certificates. It has no representation of open texture. A concrete example illustrates the complementarity: in IRC §163(h), the condition "property is a qualified residence" is vague (Hart's penumbra includes mobile homes, timeshares, and boats). In Catala, this condition must either be encoded as a Boolean input (the user asserts it) or omitted (the program raises an error for unhandled cases). In LegalLean, `isDeductible` returns `FormalisationBoundary.boundary "qualified residence" "IRS / Tax Court"` -- the system records that it cannot determine this condition, names the authority responsible, and the `Vague` instance on `IsQualifiedResidence` documents the core and penumbra for audit. The distinction is not that LegalLean "handles" vagueness better, but that it represents the inability to handle it as a typed, auditable object rather than a silent gap.

**L4L** [12] (Hou et al.): the closest prior work in spirit. L4L uses dependent types and produces proofs, but SMT-backed verification means the proof certificates are not auditable proof terms in the Curry-Howard sense. Its treatment of open texture relies on the SMT solver's inability to discharge certain goals rather than a typed annotation.

**LegalRuleML** [16] (Palmirani et al.): a rich XML ontology with sophisticated modelling of deontic modalities and temporal applicability. It is a knowledge representation language, not a reasoning system -- it provides no automated inference or proof production.

### 5.3 Limitations

The principal limitations of LegalLean are:

**Scalability**: the three case studies cover a total of nine provisions and fewer than 300 lines of Lean code each. Scaling to a complete statute (26 U.S.C. §163 alone is thousands of words) would require substantially more proof engineering. Each open-texture term requires a hand-crafted axiom and typeclass instance; this does not automate.

**No LLM-to-Lean pipeline**: the framework does not yet include an automated formalisation pipeline. The transducer half of the architecture -- converting statutory text to Lean 4 -- is currently manual. A practical system requires this to be automated with language models, with LegalLean as the verification layer.

**Axiom dependence**: the open-texture axioms are genuine axioms: they cannot be proved by Lean's kernel. The framework is only as sound as the legal judgments behind the `Vague` and `Discretionary` instances. If those instances are wrong about what constitutes the core or penumbra of a vague term, the theorems built on them may be formally valid but legally misleading.

**No temporal algebra**: the TCJA cutoff is encoded as a numeric comparison (`year.year >= 2018`), not via a proper temporal type with duration, retroactivity, and sunset provisions. A complete temporal logic layer remains future work.

**Sorry-bypass gap**: the type system does not prevent the construction `FormalisationBoundary.formal sorry`. A careless or adversarial user could mark a proposition as formally verified by using Lean's `sorry` axiom, which discharges any proof obligation without evidence. The VERIFICATION.md protocol addresses this by requiring `grep -r sorry` as part of the verification layer, but the type system itself does not enforce it. A stronger design would use a custom elaboration that rejects `sorry` inside `formal` constructors, or a linting pass that flags `sorry` usage as a build failure. This is an engineering limitation, not a theoretical one: the guarantee of "zero sorry" is a property of the codebase at a point in time, verified by inspection, not a property enforced by the type system itself.

**Normative risk of formalisation**: by encoding Hart's open texture as a typed object, this work makes the formalisation boundary tractable and auditable. This carries a normative risk that Lessig's "code is law" tradition identifies: making the boundary typed may create a false sense of completeness. A user who sees `FormalisationBoundary.boundary "requires IRS determination" "IRS / Tax Court"` might treat the annotation as sufficient engagement with the underlying vagueness, when in fact the core/penumbra analysis in the `Vague` instance is one interpretation among several. The system does not resolve open texture; it classifies and annotates it. Users must understand that the annotation is a map of the boundary, not a resolution of it. This limitation is intrinsic to any formalisation of vagueness and should be communicated clearly in any deployment context.

---

## 6. Related Work

**Defeasible Deontic Logic (DDL)**: Governatori's DDL [9, 10] is the most complete prior work on defeasible reasoning in law. It provides a proof theory for defeasible rules with deontic modalities and has been applied to compliance checking in eHealth, business contracts, and regulatory codes. The TCP Code comparison in Section 4.3 is designed to be directly comparable with Governatori's encodings. LegalLean's advance over DDL is not in defeasibility machinery but in (1) machine-checkable proof certificates, (2) the FormalisationBoundary typing of open texture, and (3) dependent types enabling evidence-as-inhabitants.

**Catala** [14]: Merigoux et al.'s Catala is the most practical prior system for statutory formalisation, with a growing library of French, US, and Polish tax law. Its design priority is executability: a Catala specification is a runnable program that computes legal outcomes from facts. LegalLean's priority is verifiability: it produces proof terms, not program outputs. The two approaches are complementary rather than competitive.

**L4L** [12]: Hou et al.'s Logic for Law (L4L) is the work closest in motivation to LegalLean. It uses dependent types and produces machine-checked reasoning about legal texts. The primary technical difference is that L4L's verification layer relies on SMT, while LegalLean's relies on Lean 4's kernel verifier. SMT provides more automation; Lean 4's kernel provides more auditability. L4L does not include a typed treatment of open texture.

**LegalRuleML** [16]: Palmirani and Governatori's LegalRuleML extends RuleML with deontic operators, temporal metadata, and defeasibility annotations. It is the most expressive knowledge representation format for legal rules but provides no automated reasoning. LegalLean and LegalRuleML address different problems: LegalLean verifies reasoning; LegalRuleML represents knowledge for interchange.

**Hohfeldian frameworks**: Prior work by McCarty [15] and Boella et al. applies Hohfeld's fundamental legal relations (rights, duties, powers, immunities) in formal settings. LegalLean's three-modality deontic type (`permitted`, `prohibited`, `obligatory`) is intentionally minimal; a Hohfeldian extension is straightforward but not required for the case studies.

**Logic programming approaches**: Kowalski and Sergot's Event Calculus [18], together with Sergot et al.'s British Nationality Act encoding [19], established the research programme of encoding law in logic programming. That tradition addressed defeasibility before DDL but did not handle open texture or produce machine-checked proofs.

---

## 7. Conclusion and Future Work

LegalLean demonstrates that Lean 4 dependent types provide a viable verification layer for legal reasoning systems. The key result is not the theorem count but the architecture: a system in which Hart's open texture is a first-class typed object rather than an external limitation, and in which the distinction between "machine-verified" and "requires human determination" is enforced by the type checker rather than stated in documentation.

The `monotonicity_break_general` theorem illustrates what machine-checked legal reasoning makes possible: a formal, auditable certificate that the TCJA 2017 removed a deduction permission for all home equity interest payments, not merely for specific test cases. This kind of structural certificate -- not an answer, but a proof about the legal system itself -- is what distinguishes a verifier from a transducer.

Several directions remain open. First, the transducer layer: language models are the natural tool for converting statutory text to Lean 4 stubs, with the type checker providing feedback to guide the formalisation. Second, zero-knowledge proofs for compliance: a party wishing to attest compliance without disclosing underlying facts could, in principle, use ZK proofs over the formal structure. Third, temporal algebra: a proper treatment of statutory effective dates, sunset provisions, and retroactivity requires a temporal type extending the current `TaxYear` structure. Fourth, scaling studies: encoding a complete statute rather than a selected kernel would test whether the proof engineering effort is tractable in practice.

The verification protocol that emerges from this work has three layers: the type checker verifies structural properties; the `FormalisationBoundary` annotations identify where institutional determination is required; and legal practitioners review the open-texture instances to ensure the core/penumbra analysis is sound. Only the first layer is automated. The claim is not that legal reasoning can be automated but that the parts that can be verified should be, and the parts that cannot should be typed rather than silently omitted.

---

## References

[1] Aguilar Pelaez, E. (2026). LegalLean source code. Lean 4 v4.24.0.

[2] Baader, F., Calvanese, D., McGuinness, D., Nardi, D., and Patel-Schneider, P., eds. (2003). *The Description Logic Handbook*. Cambridge University Press.

[3] Bench-Capon, T. and Sartor, G. (2003). A model of legal reasoning with cases incorporating theories and values. *Artificial Intelligence*, 150(1-2), 97--143.

[4] Boella, G., van der Torre, L., and Verhagen, H. (2006). Introduction to normative multiagent systems. *Computational and Mathematical Organization Theory*, 12(2-3), 71--79.

[5] Curry, H.B. (1934). Functionality in combinatory logic. *Proceedings of the National Academy of Sciences*, 20(11), 584--590.

[6] Howard, W.A. (1980). The formulae-as-types notion of construction. In J.P. Seldin and J.R. Hindley, eds., *To H.B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism*, 479--490. Academic Press.

[7] de Moura, L., Selsam, D., Ullrich, S., and Avigad, J. (2021). The Lean 4 theorem prover and programming language. *Proceedings of CADE-28*, Lecture Notes in Computer Science. Springer.

[8] Dworkin, R. (1977). *Taking Rights Seriously*. Harvard University Press.

[9] Governatori, G. (2005). Representing business contracts in RuleML. *International Journal of Cooperative Information Systems*, 14(2-3), 181--216.

[10] Governatori, G., Rotolo, A., and Sartor, G. (2019). Compliance in eHealth: a defeasible logic approach. *Artificial Intelligence in Medicine*, 93, 34--48.

[11] Hart, H.L.A. (1961). *The Concept of Law*. Oxford University Press.

[12] Hou, Z., Governatori, G., Hashmi, M., and Lam, H.P. (2021). Logic for Law (L4L): a dependent-type-based framework for modelling and reasoning about law. *Proceedings of JURIX 2021*, Frontiers in Artificial Intelligence and Applications. IOS Press.

[13] Lawsky, S.B. (2017). A logic for statutes. *Florida Tax Review*, 21(1), 60--113.

[14] Merigoux, D., Chataing, N., and Protzenko, J. (2021). Catala: a programming language for the law. *Proceedings of ICFP 2021*. ACM.

[15] McCarty, L.T. (1977). Reflections on TAXMAN: an experiment in artificial intelligence and legal reasoning. *Harvard Law Review*, 90(5), 837--893.

[16] Palmirani, M. and Governatori, G. (2018). Modelling legal knowledge for GDPR compliance checking. *Proceedings of JURIX 2018*, Frontiers in Artificial Intelligence and Applications. IOS Press.

[17] Reiter, R. (1980). A logic for default reasoning. *Artificial Intelligence*, 13(1-2), 81--132.

[18] Shanahan, M. (1999). The event calculus explained. *Artificial Intelligence Today*, Lecture Notes in Computer Science, vol. 1600, 409--430. Springer.

[19] Sergot, M.J., Sadri, F., Kowalski, R.A., Kriwaczek, F., Hammond, P., and Cory, H.T. (1986). The British Nationality Act as a logic program. *Communications of the ACM*, 29(5), 370--386.
```


mcp startup: no servers





thinking
**Classifying 28 theorems from IRC163h and O1Visa**

I identified exactly 28 theorems split across IRC163h (15) and O1Visa (13) code files, matching the user’s 28-theorem count by excluding TCPCode theorems. I'll classify these based on their domain and proof focus within each codebase, citing file paths and theorem names specifically for precision. Next, I'll prepare detailed critical analysis referencing lines and files as requested.
thinking
**Highlighting formalization and reasoning weaknesses**

This chunk reveals critical flaws: the formalization boundary lacks enforcement, permitting unchecked axioms or "sorry" proofs that invalidate verification claims; many theorems are trivial or definitional without genuine defeasible reasoning; key constructs like open texture typeclasses and defeasible relations are unused or only metadata; the isDeductible function is manual branching rather than rule-based inference; overall, the code fails to realize robust verified legal reasoning or a defeasible logic engine. Next steps involve framing detailed numbered answers with explicit code citations and delivering pointed academic critique accordingly.
thinking
**Classifying all 28 theorems with rationale**

I systematically classified each theorem as trivial, moderate, or substantive, finding most trivial—based on proofs by simp, rfl, or enum equality—and only a few moderate showing structural properties of decision procedures; none qualify as substantive genuine legal reasoning. This stark classification highlights the absence of a real defeasible reasoning engine or deep legal inference in the code. Next, I’ll prepare detailed, numbered answers with explicit references matching the user’s question format.
thinking
**Q1 Theorem Classification**

| #  | Theorem (File)                         | Classification | Reason                                                                                      |
|-----|--------------------------------------|----------------|---------------------------------------------------------------------------------------------|
| 1   | tcja_prohibits_home_equity (`IRC163h.lean`)           | Trivial       | Proof by `simp` unfolding `isDeductible` with hard-coded `if`; definitional                  |
| 2   | non_individual_never_deducts (`IRC163h.lean`)          | Trivial       | `simp` on function definitions; no deep reasoning                                           |
| 3   | unsecured_never_deducts (`IRC163h.lean`)               | Trivial       | Same as above; straightforward unfolding                                                   |
| 4   | defeat_direct_acyclicity (`IRC163h/Theorems.lean`)     | Trivial       | Enumerates defeat list; `simp` proof; no inference                                          |
| 5   | defeat_chain_exists (`IRC163h/Theorems.lean`)          | Trivial       | Defined by exact constants; trivial exactness proof                                         |
| 6   | grandfather_does_not_directly_defeat_base (`IRC163h/Theorems.lean`) | Trivial       | Case split on listed items; no logic                                                        |
| 7   | R1_R2_deontic_conflict (`IRC163h/Theorems.lean`)       | Trivial       | `simp` on inequality of enums                                                              |
| 8   | pre_tcja_no_prohibition (`IRC163h/Theorems.lean`)      | Trivial       | Uses `omega` on simple numeric property `postTCJA`; trivial                                |
| 9   | no_mixed_outcomes (`IRC163h/Theorems.lean`)            | Moderate      | Exhaustive case split on function outputs; structural property, not semantics              |
| 10  | boundary_authority_is_irs_tax_court (`IRC163h/Theorems.lean`) | Trivial       | Equality of boundary strings; no legal reasoning                                           |
| 11  | all_rules_are_permissions_or_prohibitions (`IRC163h/Theorems.lean`) | Trivial       | `simp` on rule modalities; no substantive property                                        |
| 12  | auto_reject_conditions (`IRC163h/Theorems.lean`)       | Trivial       | Proof by simplification on decision paths                                                  |
| 13  | monotonicity_break_tcja (`IRC163h/Theorems.lean`)      | Trivial       | `rfl` proof on hard-coded conditional; no reasoning on defeats                            |
| 14  | monotonicity_break_general (`IRC163h/Theorems.lean`)   | Moderate      | Quantified case analysis on conditionals; structural but no real semantics                 |
| 15  | pre_tcja_not_auto_rejected (`IRC163h/Theorems.lean`)   | Trivial       | `simp` proof unfolding definitions                                                        |
| 16  | three_criteria_lower_bound (`O1Visa.lean`)             | Trivial       | Projection of list cardinality; direct field access                                        |
| 17  | final_merits_is_boundary (`O1Visa.lean`)               | Trivial       | `rfl` on value equality                                                                   |
| 18  | R1_R2_deontic_distinct (`O1Visa.lean`)                 | Trivial       | `simp` on distinct enum values                                                            |
| 19  | defeat_direct_acyclicity (`O1Visa.lean`)               | Trivial       | Single-item list enumeration; trivial proof                                               |
| 20  | eligibility_always_mixed (`O1Visa.lean`)                | Trivial       | `rfl` proof; function always returns `mixed` regardless of evidence                        |
| 21  | empty_list_ineligible (`O1Visa.lean`)                   | Trivial       | `omega` on list length; basic structural                                               |
| 22  | comparable_evidence_changes_pathway (`O1Visa.lean`)    | Trivial       | `simp` on function behavior                                                               |
| 23  | allDistinct_pair_implies_ne (`O1Visa.lean`)            | Trivial       | Basic list property                                                                        |
| 24  | majorAward_ne_membership (`O1Visa.lean`)                | Trivial       | `decide` on enum equality                                                                 |
| 25  | majorAward_ne_mediaCoverage (`O1Visa.lean`)            | Trivial       | `decide` on enum equality                                                                 |
| 26  | judgingRole_ne_scholarlyAuthorship (`O1Visa.lean`)    | Trivial       | `decide` on enum equality                                                                 |
| 27  | no_witness_below_three (`O1Visa.lean`)                  | Trivial       | `omega` on numeric field                                                                   |
| 28  | two_criteria_insufficient (`O1Visa.lean`)              | Trivial       | `omega` on cardinality; simple property                                                   |

---

**Q2 FormalisationBoundary vs. labeled union type**

The `FormalisationBoundary` type in `LegalLean/Core.lean` is essentially a labeled sum type with constructors `formal (proof : P)`, `boundary (String × String)`, and `mixed (String × String)`. It lacks parametric enforcement linking `boundary` or `mixed` to any predicate or the `RequiresHumanDetermination` typeclass. Functions like `isDeductible` and `determineEligibility` use hard-coded strings for boundaries without referencing `RequiresHumanDetermination` instances, making the typeclass purely documentary without impact on proof search or enforcement. Thus, `FormalisationBoundary` offers no stronger guarantee than a union type in Haskell; Lean's dependent types are underused here, and the lack of constrained instances means mislabeling of boundaries is possible. The open texture modeling (`Vague`, `Discretionary`) is defined but unused in computations, further limiting usefulness.

---

**Q3 Sorry-bypass gap critique**

Although there are no `sorry` proofs in these files, the heavy use of axioms to define legal predicates (`axiom` in Lean) and the general lack of restrictions on their use (including in `formal` boundaries) seriously undermine soundness claims. The admitted "sorry-bypass gap" is not fully addressed, as axioms and classical reasoning remain prolific. This invalidates claims of strict machine-checked, sound formalization since axioms may introduce unsoundness without enforcement. The lack of enforcement on how boundaries are constructed aggravates this; thus, the "machine-checkable guarantees" claim is misleading.

---

**Q4 Proposed next 5 theorems to improve formalisation**

1. **Soundness of `isDeductible` relative to rules and defeat graph**: formalize that `isDeductible` outputs derive exactly from a defeasible inference over declared `LegalRule`s and `Defeats`.

2. **Deontic consistency theorem**: prove no payment can be simultaneously permitted and prohibited after defeat resolution, ensuring consistent outcomes.

3. **Boundary correctness alignment**: establish that any `boundary` result corresponds strictly to predicates with `RequiresHumanDetermination` instances, linking boundary outputs to semantic metadata.

4. **O1Visa criteria soundness and minimality**: show that `MeetsThreeCriteria` corresponds exactly to existence of three distinct formal criteria supported by evidence, independent of list ordering.

5. **Defeat relation completeness and soundness**: prove that every defeated rule in `defeatedBy` is reflected in the `Defeats` list and influences outcomes, providing semantic correctness to defeat mapping beyond mere data.

---

**Q5 Critical comparison to related systems**

The paper’s comparison to DDL, Catala, L4L, and LegalRuleML is unbalanced and unsupported by code evidence. Claims of superiority across seven dimensions rely on selective metrics without empirical validation or benchmarks. The lack of an actual defeasible reasoning engine or a semantics module, plus reliance on hand-coded functions ignoring `LegalRule` and `Defeats`, contrasts sharply with these mature, executable, or SMT-backed systems. Temporal reasoning claims are inflated: `postTCJA` is a simple integer comparison, not temporal logic. The review also notes omission of relevant legal reasoning frameworks like ASPIC+, s(CASP), and Isabelle/HOL work, which would provide more substantive baselines.

---

**Q6 Evaluation of monotonicity break theorem**

The monotonicity break theorems (e.g., `monotonicity_break_general`) merely state structural properties about if-then branching in hard-coded code paths and are proven by `simp` or `rfl`. They do not involve `LegalRule` or defeat reasoning. Thus, the theorems are straightforward and trivial, lacking substantive insight about legal reasoning monotonicity.

---

**Q7 JURIX 2026 rating: Strong Reject**

Justifications:

1. The main contribution (`FormalisationBoundary`) is a weakly enforced labeled union providing mainly documentation, lacking parametric guarantees or proof search constraints.

2. No defeasible reasoning engine is implemented; `LegalRule` and `Defeats` are data containers unused in deductions.

3. Theorems are mostly trivial properties of code or data unfolding, proven by simple tactics (`simp`, `rfl`, `decide`, `omega`), with no substantive demonstration of verified legal reasoning.

4. The paper claims 44 theorems, but the code contains only 39; the user’s question references 28 with no mention of the discrepancy, reflecting technical sloppiness.

5. The admitted "sorry-bypass gap" via axioms remains unaddressed, undermining trustworthiness.

Minimal strengths include the explicit boundary annotations and compiling code, but these do not offset the weaknesses. The paper
thinking
**Q1 Theorem Classification**

| Theorem (File)                                         | Classification | Reason                                                                                             |
|-------------------------------------------------------|----------------|--------------------------------------------------------------------------------------------------|
| `tcja_prohibits_home_equity` (`IRC163h.lean`)          | Trivial       | `simp` unfolding `isDeductible` with `if`; just definition unfolding, no semantic reasoning        |
| `non_individual_never_deducts` (`IRC163h.lean`)        | Trivial       | `simp` on function paths                                                                          |
| `unsecured_never_deducts` (`IRC163h.lean`)             | Trivial       | Same as above                                                                                    |
| `defeat_direct_acyclicity` (`IRC163h/Theorems.lean`)   | Trivial       | Enumerative `simp` proof on defeat lists                                                         |
| `defeat_chain_exists` (`IRC163h/Theorems.lean`)        | Trivial       | Defined by exact pairs/constants; trivial enumeration                                              |
| `grandfather_does_not_directly_defeat_base` (`IRC163h/Theorems.lean`) | Trivial       | Case splits with no logic reuse                                                                   |
| `R1_R2_deontic_conflict` (`IRC163h/Theorems.lean`)     | Trivial       | Enum inequality via `simp`                                                                        |
| `pre_tcja_no_prohibition` (`IRC163h/Theorems.lean`)    | Trivial       | Numeric property proved by `omega`                                                               |
| `no_mixed_outcomes` (`IRC163h/Theorems.lean`)          | Moderate      | Full case split on code branches; structural but no deep semantics                                |
| `boundary_authority_is_irs_tax_court` (`IRC163h/Theorems.lean`) | Trivial       | Equality of strings after unfolding; not semantic                                                 |
| `all_rules_are_permissions_or_prohibitions` (`IRC163h/Theorems.lean`) | Trivial       | `simp` on rule fields (modality); trivial                                                        |
| `auto_reject_conditions` (`IRC163h/Theorems.lean`)     | Trivial       | Simplification of code path                                                                       |
| `monotonicity_break_tcja` (`IRC163h/Theorems.lean`)    | Trivial       | `rfl` on conditionals; no logical reasoning                                                      |
| `monotonicity_break_general` (`IRC163h/Theorems.lean`) | Moderate      | Quantified property over code paths, but proven by `simp`; structural, not semantic               |
| `pre_tcja_not_auto_rejected` (`IRC163h/Theorems.lean`) | Trivial       | `simp` unfolding                                                                                |
| `three_criteria_lower_bound` (`O1Visa.lean`)           | Trivial       | Projection of list length                                                                         |
| `final_merits_is_boundary` (`O1Visa.lean`)             | Trivial       | `rfl` on value identity                                                                           |
| `R1_R2_deontic_distinct` (`O1Visa.lean`)               | Trivial       | `simp` on distinct enums                                                                          |
| `defeat_direct_acyclicity` (`O1Visa.lean`)             | Trivial       | Single-case enumeration                                                                           |
| `eligibility_always_mixed` (`O1Visa.lean`)             | Trivial       | `rfl`; function returns `mixed` always                                                           |
| `empty_list_ineligible` (`O1Visa.lean`)                 | Trivial       | `omega` on cardinality                                                                            |
| `comparable_evidence_changes_pathway` (`O1Visa.lean`) | Trivial       | `simp` on function paths                                                                          |
| `allDistinct_pair_implies_ne` (`O1Visa.lean`)          | Trivial       | Basic list property                                                                               |
| `majorAward_ne_membership` (`O1Visa.lean`)             | Trivial       | Enum equality via `decide`                                                                        |
| `majorAward_ne_mediaCoverage` (`O1Visa.lean`)          | Trivial       | Enum equality                                                                                     |
| `judgingRole_ne_scholarlyAuthorship` (`O1Visa.lean`)  | Trivial       | Enum equality                                                                                     |
| `no_witness_below_three` (`O1Visa.lean`)               | Trivial       | `omega` on numeric cardinality                                                                   |
| `two_criteria_insufficient` (`O1Visa.lean`)            | Trivial       | `omega` on list cardinality                                                                       |

**Summary:** Out of 28, 26 are trivial (proof by simplification, unfolding, or enumeration), 2 are moderate (structural case splits), and none are substantive semantic proofs of legal reasoning. Most proofs rely on `simp`, `rfl`, `decide`, or `omega` tactics and do not connect to the `LegalRule` or `Defeats` data.

---

**Q2 Analysis of FormalisationBoundary usage**

The `FormalisationBoundary` type (in `LegalLean/Core.lean`) is parameterized by a universe `P : Sort _` and has form `formal (proof : P) | boundary (String × String) | mixed (String × String)`. However, in all usage (`isDeductible`, `determineEligibility`), it is instantiated as `FormalisationBoundary Prop`. This means the `formal` constructor stores an element of type `Prop` (a proposition), not a *proof* of that proposition.

For example, `isDeductible` returns `FormalisationBoundary.formal False`—this wraps the proposition `False`, not a proof of `False`. This breaks the expected Curry-Howard correspondence where `formal` would carry proof evidence. Therefore, the claim to machine-verified proofs is unsupported as the formal cases never contain actual proof terms.

Moreover, the `boundary` and `mixed` constructors carry unstructured string metadata, not linked to any predicate or proof obligation. The `RequiresHumanDetermination` typeclass and open texture classes (`Vague`, `Discretionary`) are defined but never enforced or connected to computations or proofs. They are used solely as metadata without constraining reasoning.

Thus, `FormalisationBoundary` acts as a tagged union holding propositions (not proofs) plus strings, undermining formal guarantees. This is a major conceptual flaw limiting trust in the purported semantics.

---

**Q3 Regarding the sorry-bypass gap**

Though all theorems are proven without the use of `sorry`, the formalisation depends heavily on axioms to define predicates representing legal concepts, leaving foundational gaps unaddressed. The admitted "sorry-bypass gap" is replaced with axiom usage that is not justified or checked.

Combined with the `FormalisationBoundary` misuse (no proof embedding) and the absence of defeasible inference mechanisms applying `LegalRule` and `Defeats`, this undermines claims of a fully machine-verified reasoning system. The framework cannot guarantee soundness of deductions despite no explicit `sorry`.

---

**Q4 Five missing theorems to enhance formalisation**

1. **Soundness connecting `isDeductible` to defeasible semantics:** Prove that all outputs from `isDeductible` correspond exactly to inferences derived from `LegalRule` and `Defeats` via a formal defeasible reasoning engine.

2. **Consistency of outcome theorem:** Establish no scenario yields both permission and prohibition simultaneously after applying defeat resolution.

3. **Boundary integrity theorem:** Demonstrate every `boundary` or `mixed` output corresponds exactly to predicates tagged by `RequiresHumanDetermination`, enforcing the typeclass semantic link.

4. **O1Visa criteria equivalence theorem:** Prove correspondence between formal criteria predicates and evidence lists, ensuring minimal and independent criteria sets match semantic interpretation.

5. **Defeat relation soundness and completeness:** Show `defeatedBy` fields correspond precisely to the explicit `Defeats` list and that defeat handling is reflected in all deductions.

---

**Q5 Critical evaluation of comparison to related systems**

The paper’s claims of superiority over DDL, Catala, L4L, and LegalRuleML lack support in the codebase. The absence of a defeasible reasoning engine and the disconnection of rules and defeats from deduction contrast with mature, semantics-grounded approaches.

Temporal reasoning is simplistic (integer comparisons instead of formal temporal logic). The lack of connections to well-known formal frameworks (e.g., ASPIC+, s(CASP)) or robust formalizations reduces comparative validity.

The discussion is selective and omits important references, weakening the analysis and overstating contributions.

---

**Q6 On the monotonicity break theorem**

Monotonicity break proofs such as `monotonicity_break_general` rely solely on `simp` and `rfl` tactics over case analyses of hard-coded function paths. There is no semantic insight or use of legal rules or defeat relations.

Therefore, these theorems are trivial and do not establish meaningful non-monotonicity properties of the legal reasoning model.

---

**Q7 JURIX 2026 rating: Strong Reject**

Reasons:

- **Misuse of formal structures:** `FormalisationBoundary` is instantiated at the proposition level, resulting in no actual embedded proofs, invalidating the claim of machine-verified deductions.

- **Unused core data:** `LegalRule` and `Defeats` exist but have no semantic role or inference engine applying them.

- **Theorem quality:** Nearly all proofs are trivial and based on code unfolding or enumeration rather than verified legal reasoning.

- **Foundational uncertainty:** Persistent reliance on axioms without closure leaves soundness unproven despite no `sorry`.

- **Inconsistent claims:** Paper states 44 theorems; code files enumerate fewer (39), with 28 analyzed here; indicates carelessness.

Although the project shows initiative in formalizing legal reasoning, the
codex
Below is the harshest, code‑driven review I can give. I focus on what the code *actually enforces*, not what the paper claims.

**Q1. Theorem Classification (28 total)**  
Summary: 26 trivial, 2 moderate, 0 substantive. Most proofs are definitional (`rfl`/`simp`/`decide`/`omega`) and do not use any defeasible reasoning or evidence.  
Note: Many “formal” results are about `FormalisationBoundary Prop`, so `formal False` is just the *proposition* `False`, not a proof of falsity. See `isDeductible`’s type in `LegalLean/CaseStudies/IRC163h.lean` and `determineEligibility` in `LegalLean/CaseStudies/O1Visa.lean`.

| # | Theorem (file) | Classification | Why |
|---|---|---|---|
| 1 | `tcja_prohibits_home_equity` (`LegalLean/CaseStudies/IRC163h.lean`) | Trivial | `simp` unfolds nested `if` in `isDeductible`; no rule semantics. |
| 2 | `non_individual_never_deducts` (`LegalLean/CaseStudies/IRC163h.lean`) | Trivial | One‑branch path trace via `simp`. |
| 3 | `unsecured_never_deducts` (`LegalLean/CaseStudies/IRC163h.lean`) | Trivial | Same as above. |
| 4 | `defeat_direct_acyclicity` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Enumerates `allDefeats` list and `simp` each case. |
| 5 | `defeat_chain_exists` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `exact ⟨defeat_R3_E1_1, ...⟩`; just witnesses constants. |
| 6 | `grandfather_does_not_directly_defeat_base` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Case split on list, `simp_all`. |
| 7 | `R1_R2_deontic_conflict` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `simp` on record fields; enum inequality. |
| 8 | `pre_tcja_no_prohibition` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `postTCJA` is `year ≥ 2018`; `omega` on arithmetic. |
| 9 | `no_mixed_outcomes` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Moderate | Exhaustive case split of `isDeductible`; still only code‑path analysis. |
|10 | `boundary_authority_is_irs_tax_court` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Proof is string equality after unfolding; not legal reasoning. |
|11 | `all_rules_are_permissions_or_prohibitions` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `simp` on three records. |
|12 | `auto_reject_conditions` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Three `simp` paths through `isDeductible`. |
|13 | `monotonicity_break_tcja` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `rfl` on a hand‑picked sample; pure definitional evaluation. |
|14 | `monotonicity_break_general` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Moderate | Quantified, but still `simp` on `isDeductible`; no use of `LegalRule`/`Defeats`. |
|15 | `pre_tcja_not_auto_rejected` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `simp` again; follows from branch structure. |
|16 | `three_criteria_lower_bound` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | Projection of `cardinal` field. |
|17 | `final_merits_is_boundary` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `rfl` on definition of `finalMeritsDetermination`. |
|18 | `R1_R2_deontic_distinct` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `simp` on modalities. |
|19 | `defeat_direct_acyclicity` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | Single‑element list case. |
|20 | `eligibility_always_mixed` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `rfl`; `determineEligibility` is definitionally `mixed`. |
|21 | `empty_list_ineligible` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `omega` from `cardinal`. |
|22 | `comparable_evidence_changes_pathway` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `simp` on record fields and list membership. |
|23 | `allDistinct_pair_implies_ne` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | Basic list‑membership reasoning, no legal content. |
|24 | `majorAward_ne_membership` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `decide` on enum inequality. |
|25 | `majorAward_ne_mediaCoverage` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `decide`. |
|26 | `judgingRole_ne_scholarlyAuthorship` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `decide`. |
|27 | `no_witness_below_three` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `omega` from `cardinal`. |
|28 | `two_criteria_insufficient` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `omega` from `cardinal`. |

**Q2. Is `FormalisationBoundary` a genuine contribution or just a labelled union?**  
It is, in the current code, essentially a labelled union with strings. Worse: it is used at `FormalisationBoundary Prop`, so `formal` stores a proposition, **not a proof**. That destroys the claimed Curry‑Howard guarantee.

Evidence:
- `isDeductible : ... → FormalisationBoundary Prop` in `LegalLean/CaseStudies/IRC163h.lean`.
- The “formal” result is `FormalisationBoundary.formal False` throughout `isDeductible`, which is only a `Prop` value, not a proof of `False`.
- `determineEligibility : ... → FormalisationBoundary Prop` in `LegalLean/CaseStudies/O1Visa.lean` returns `mixed` strings; it is not connected to proofs.

A Haskell `data Result a = Formal a | NeedsHuman String String | Mixed String String` does essentially the same thing here. Lean’s dependent types add almost nothing because you are not using `FormalisationBoundary` at the level of *particular propositions*.

`RequiresHumanDetermination` is pure documentation. There is no use of `[RequiresHumanDetermination P]` to constrain construction of `formal` outcomes, and no link from `Vague`/`Discretionary` instances to the `boundary` constructor. `isDeductible` and `determineEligibility` hard‑code strings and never consult the typeclass instances. This is metadata without enforcement.

**Q3. Is the “`FormalisationBoundary.formal sorry`” gap fatal?**  
For the claims in this paper, yes. The paper asserts “machine‑verified” reasoning, but the code already sidesteps proof even without `sorry` by using `FormalisationBoundary Prop`. That is a stronger failure than the `sorry` loophole. The system does not check proofs; it stores propositions and strings.

Stronger design:
1. Use `FormalisationBoundary P` where `P` is the *specific proposition*, not `Prop`. This forces `formal` to carry a proof term of that proposition.  
2. Gate `formal` with a dedicated typeclass, e.g., `Formalisable P`, and **only** provide instances for closed, decidable predicates.  
3. Tie `boundary` to `[RequiresHumanDetermination P]` and eliminate ad‑hoc strings. Use the typeclass fields as the authoritative metadata.  
4. Enforce “no `sorry` and no extra axioms” in CI via Lean’s `--no-sorry` plus `#print axioms` checks.  
None of this exists in the current code.

**Q4. Missing properties that would make this useful (next 5 theorems)**  
These are the minimum to make the framework *do* legal reasoning rather than report on a hard‑coded decision tree.

1. **Soundness of rule evaluation**  
If a defeasible proof exists from `LegalRule` + `Defeats`, then `isDeductible` (or a proper evaluator) returns a corresponding `FormalisationBoundary` outcome. Requires an actual semantics of `LegalRule`/`Defeats`, which currently does not exist.

2. **Completeness of rule evaluation**  
If the evaluator returns `formal` (or `boundary`), then there is a defeasible proof tree explaining it. Right now `isDeductible` never uses `LegalRule` or `Defeats` (`LegalLean/CaseStudies/IRC163h.lean`), so there is no proof object to recover.

3. **Boundary correctness**  
For any `boundary` result, there exists a predicate `P` with `[RequiresHumanDetermination P]` whose `reason`/`authority` match the output. This would link open‑texture typeclasses to actual outcomes. Currently, boundary strings are ad‑hoc and can drift.

4. **Criteria evidence linkage (O‑1)**  
Show that formal evidence constructors imply the criterion predicates. Right now `hasMediaCoverage`, `hasQualifyingAward`, etc. are unused; `criterionProp` is disconnected from the formal data in `LegalLean/CaseStudies/O1Visa.lean`.

5. **Defeat alignment invariant**  
Prove that for every `Defeats` entry, the defeated rule’s `defeatedBy` contains the defeater ID, and vice‑versa. This would at least make the defeat metadata coherent, which is not established anywhere.

**Q5. Comparison to DDL, Catala, L4L, LegalRuleML**  
The comparison is not fair and the “superiority on 7 dimensions” is self‑serving.

Concrete mismatches with your own code:
- **“Machine‑checkable guarantees” = 5** is contradicted by using `FormalisationBoundary Prop` and returning `formal False` without proofs. There are no proof objects of deductibility or non‑deductibility.  
- **“Temporal reasoning” = 5** is contradicted by `postTCJA : year.year ≥ 2018` in `LegalLean/CaseStudies/IRC163h.lean`, which is trivial date arithmetic, not temporal logic.  
- **“Compositional semantics” = 5** is contradicted by the absence of any evaluator connecting `LegalRule`/`Defeats` to outcomes. The rules are data; the reasoning is a hand‑coded `if` tree.

Missing comparisons:
- Argumentation frameworks (ASPIC+, Dung‑style) that are commonly used in legal reasoning.  
- Logic‑programming legal systems (e.g., s(CASP)/Prolog‑based statutory encodings).  
- Proof‑assistant legal formalizations in Isabelle/HOL or Coq that *do* carry proofs of propositions instead of propositions as values.  
These omissions are critical given the claimed novelty of “verification.”

**Q6. Is the monotonicity break theorem non‑trivial?**  
No. The proof is two `simp` calls because the outcome is *hard‑coded* in `isDeductible` with `if year.year ≥ 2018 then FormalisationBoundary.formal False`. There is no reasoning over a defeasible rule set. The theorem is a property of a hand‑written decision procedure, not of a legal logic system. The “non‑triviality is in the universality” claim is not convincing because universality is over a function that already bakes in the legal change; it is not derived from adding a rule.

**Q7. Would this be accepted at JURIX 2026?**  
**Rating: Strong Reject.**

Key weaknesses (code‑anchored):
- The central claim of “formal verification” is undermined because outcomes are `FormalisationBoundary Prop`, so `formal` carries propositions not proofs (`LegalLean/CaseStudies/IRC163h.lean`, `LegalLean/CaseStudies/O1Visa.lean`).  
- `RequiresHumanDetermination`, `Vague`, and `Discretionary` are never used to constrain or derive outcomes. They are documentation only (`LegalLean/Core.lean` plus case studies).  
- The defeasible machinery is unused. `LegalRule` and `Defeats` are declared but not used to compute or prove anything about outcomes (`LegalLean/CaseStudies/IRC163h.lean`, `LegalLean/CaseStudies/O1Visa.lean`).  
- Theorems are overwhelmingly definitional. Many are `rfl`/`simp`/`decide` and test code paths rather than legal properties.  
- The paper’s theorem count is inconsistent. The code in the provided files yields 39 theorems (15 IRC + 13 O‑1 + 11 TCP), not 44. That is basic sloppiness.  
- The comparison table assigns perfect scores to LegalLean while the code fails to implement those dimensions in any substantive sense.

Honesty about limitations feels performative. The paper admits the `sorry` loophole and “no temporal algebra,” yet still scores itself 5/5 for “machine‑checkable guarantees” and “temporal reasoning.” The self‑assessment contradicts the actual implementation.

**Q8. Single most important improvement**  
Replace the hand‑coded decision procedures with a **verified defeasible inference engine** that consumes `LegalRule` + `Defeats` and produces `FormalisationBoundary P` for *specific propositions* `P`, with proofs for `formal`. This change would force the claimed verification to exist and would make the case studies about legal reasoning rather than about an ad‑hoc `if` tree.

---

If you want, I can sketch what the minimal defeasible semantics and the corrected `FormalisationBoundary` type would look like in Lean, but that’s beyond what this submission currently shows.
tokens used
63,079
Below is the harshest, code‑driven review I can give. I focus on what the code *actually enforces*, not what the paper claims.

**Q1. Theorem Classification (28 total)**  
Summary: 26 trivial, 2 moderate, 0 substantive. Most proofs are definitional (`rfl`/`simp`/`decide`/`omega`) and do not use any defeasible reasoning or evidence.  
Note: Many “formal” results are about `FormalisationBoundary Prop`, so `formal False` is just the *proposition* `False`, not a proof of falsity. See `isDeductible`’s type in `LegalLean/CaseStudies/IRC163h.lean` and `determineEligibility` in `LegalLean/CaseStudies/O1Visa.lean`.

| # | Theorem (file) | Classification | Why |
|---|---|---|---|
| 1 | `tcja_prohibits_home_equity` (`LegalLean/CaseStudies/IRC163h.lean`) | Trivial | `simp` unfolds nested `if` in `isDeductible`; no rule semantics. |
| 2 | `non_individual_never_deducts` (`LegalLean/CaseStudies/IRC163h.lean`) | Trivial | One‑branch path trace via `simp`. |
| 3 | `unsecured_never_deducts` (`LegalLean/CaseStudies/IRC163h.lean`) | Trivial | Same as above. |
| 4 | `defeat_direct_acyclicity` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Enumerates `allDefeats` list and `simp` each case. |
| 5 | `defeat_chain_exists` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `exact ⟨defeat_R3_E1_1, ...⟩`; just witnesses constants. |
| 6 | `grandfather_does_not_directly_defeat_base` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Case split on list, `simp_all`. |
| 7 | `R1_R2_deontic_conflict` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `simp` on record fields; enum inequality. |
| 8 | `pre_tcja_no_prohibition` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `postTCJA` is `year ≥ 2018`; `omega` on arithmetic. |
| 9 | `no_mixed_outcomes` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Moderate | Exhaustive case split of `isDeductible`; still only code‑path analysis. |
|10 | `boundary_authority_is_irs_tax_court` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Proof is string equality after unfolding; not legal reasoning. |
|11 | `all_rules_are_permissions_or_prohibitions` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `simp` on three records. |
|12 | `auto_reject_conditions` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | Three `simp` paths through `isDeductible`. |
|13 | `monotonicity_break_tcja` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `rfl` on a hand‑picked sample; pure definitional evaluation. |
|14 | `monotonicity_break_general` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Moderate | Quantified, but still `simp` on `isDeductible`; no use of `LegalRule`/`Defeats`. |
|15 | `pre_tcja_not_auto_rejected` (`LegalLean/CaseStudies/IRC163h/Theorems.lean`) | Trivial | `simp` again; follows from branch structure. |
|16 | `three_criteria_lower_bound` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | Projection of `cardinal` field. |
|17 | `final_merits_is_boundary` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `rfl` on definition of `finalMeritsDetermination`. |
|18 | `R1_R2_deontic_distinct` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `simp` on modalities. |
|19 | `defeat_direct_acyclicity` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | Single‑element list case. |
|20 | `eligibility_always_mixed` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `rfl`; `determineEligibility` is definitionally `mixed`. |
|21 | `empty_list_ineligible` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `omega` from `cardinal`. |
|22 | `comparable_evidence_changes_pathway` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `simp` on record fields and list membership. |
|23 | `allDistinct_pair_implies_ne` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | Basic list‑membership reasoning, no legal content. |
|24 | `majorAward_ne_membership` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `decide` on enum inequality. |
|25 | `majorAward_ne_mediaCoverage` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `decide`. |
|26 | `judgingRole_ne_scholarlyAuthorship` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `decide`. |
|27 | `no_witness_below_three` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `omega` from `cardinal`. |
|28 | `two_criteria_insufficient` (`LegalLean/CaseStudies/O1Visa.lean`) | Trivial | `omega` from `cardinal`. |

**Q2. Is `FormalisationBoundary` a genuine contribution or just a labelled union?**  
It is, in the current code, essentially a labelled union with strings. Worse: it is used at `FormalisationBoundary Prop`, so `formal` stores a proposition, **not a proof**. That destroys the claimed Curry‑Howard guarantee.

Evidence:
- `isDeductible : ... → FormalisationBoundary Prop` in `LegalLean/CaseStudies/IRC163h.lean`.
- The “formal” result is `FormalisationBoundary.formal False` throughout `isDeductible`, which is only a `Prop` value, not a proof of `False`.
- `determineEligibility : ... → FormalisationBoundary Prop` in `LegalLean/CaseStudies/O1Visa.lean` returns `mixed` strings; it is not connected to proofs.

A Haskell `data Result a = Formal a | NeedsHuman String String | Mixed String String` does essentially the same thing here. Lean’s dependent types add almost nothing because you are not using `FormalisationBoundary` at the level of *particular propositions*.

`RequiresHumanDetermination` is pure documentation. There is no use of `[RequiresHumanDetermination P]` to constrain construction of `formal` outcomes, and no link from `Vague`/`Discretionary` instances to the `boundary` constructor. `isDeductible` and `determineEligibility` hard‑code strings and never consult the typeclass instances. This is metadata without enforcement.

**Q3. Is the “`FormalisationBoundary.formal sorry`” gap fatal?**  
For the claims in this paper, yes. The paper asserts “machine‑verified” reasoning, but the code already sidesteps proof even without `sorry` by using `FormalisationBoundary Prop`. That is a stronger failure than the `sorry` loophole. The system does not check proofs; it stores propositions and strings.

Stronger design:
1. Use `FormalisationBoundary P` where `P` is the *specific proposition*, not `Prop`. This forces `formal` to carry a proof term of that proposition.  
2. Gate `formal` with a dedicated typeclass, e.g., `Formalisable P`, and **only** provide instances for closed, decidable predicates.  
3. Tie `boundary` to `[RequiresHumanDetermination P]` and eliminate ad‑hoc strings. Use the typeclass fields as the authoritative metadata.  
4. Enforce “no `sorry` and no extra axioms” in CI via Lean’s `--no-sorry` plus `#print axioms` checks.  
None of this exists in the current code.

**Q4. Missing properties that would make this useful (next 5 theorems)**  
These are the minimum to make the framework *do* legal reasoning rather than report on a hard‑coded decision tree.

1. **Soundness of rule evaluation**  
If a defeasible proof exists from `LegalRule` + `Defeats`, then `isDeductible` (or a proper evaluator) returns a corresponding `FormalisationBoundary` outcome. Requires an actual semantics of `LegalRule`/`Defeats`, which currently does not exist.

2. **Completeness of rule evaluation**  
If the evaluator returns `formal` (or `boundary`), then there is a defeasible proof tree explaining it. Right now `isDeductible` never uses `LegalRule` or `Defeats` (`LegalLean/CaseStudies/IRC163h.lean`), so there is no proof object to recover.

3. **Boundary correctness**  
For any `boundary` result, there exists a predicate `P` with `[RequiresHumanDetermination P]` whose `reason`/`authority` match the output. This would link open‑texture typeclasses to actual outcomes. Currently, boundary strings are ad‑hoc and can drift.

4. **Criteria evidence linkage (O‑1)**  
Show that formal evidence constructors imply the criterion predicates. Right now `hasMediaCoverage`, `hasQualifyingAward`, etc. are unused; `criterionProp` is disconnected from the formal data in `LegalLean/CaseStudies/O1Visa.lean`.

5. **Defeat alignment invariant**  
Prove that for every `Defeats` entry, the defeated rule’s `defeatedBy` contains the defeater ID, and vice‑versa. This would at least make the defeat metadata coherent, which is not established anywhere.

**Q5. Comparison to DDL, Catala, L4L, LegalRuleML**  
The comparison is not fair and the “superiority on 7 dimensions” is self‑serving.

Concrete mismatches with your own code:
- **“Machine‑checkable guarantees” = 5** is contradicted by using `FormalisationBoundary Prop` and returning `formal False` without proofs. There are no proof objects of deductibility or non‑deductibility.  
- **“Temporal reasoning” = 5** is contradicted by `postTCJA : year.year ≥ 2018` in `LegalLean/CaseStudies/IRC163h.lean`, which is trivial date arithmetic, not temporal logic.  
- **“Compositional semantics” = 5** is contradicted by the absence of any evaluator connecting `LegalRule`/`Defeats` to outcomes. The rules are data; the reasoning is a hand‑coded `if` tree.

Missing comparisons:
- Argumentation frameworks (ASPIC+, Dung‑style) that are commonly used in legal reasoning.  
- Logic‑programming legal systems (e.g., s(CASP)/Prolog‑based statutory encodings).  
- Proof‑assistant legal formalizations in Isabelle/HOL or Coq that *do* carry proofs of propositions instead of propositions as values.  
These omissions are critical given the claimed novelty of “verification.”

**Q6. Is the monotonicity break theorem non‑trivial?**  
No. The proof is two `simp` calls because the outcome is *hard‑coded* in `isDeductible` with `if year.year ≥ 2018 then FormalisationBoundary.formal False`. There is no reasoning over a defeasible rule set. The theorem is a property of a hand‑written decision procedure, not of a legal logic system. The “non‑triviality is in the universality” claim is not convincing because universality is over a function that already bakes in the legal change; it is not derived from adding a rule.

**Q7. Would this be accepted at JURIX 2026?**  
**Rating: Strong Reject.**

Key weaknesses (code‑anchored):
- The central claim of “formal verification” is undermined because outcomes are `FormalisationBoundary Prop`, so `formal` carries propositions not proofs (`LegalLean/CaseStudies/IRC163h.lean`, `LegalLean/CaseStudies/O1Visa.lean`).  
- `RequiresHumanDetermination`, `Vague`, and `Discretionary` are never used to constrain or derive outcomes. They are documentation only (`LegalLean/Core.lean` plus case studies).  
- The defeasible machinery is unused. `LegalRule` and `Defeats` are declared but not used to compute or prove anything about outcomes (`LegalLean/CaseStudies/IRC163h.lean`, `LegalLean/CaseStudies/O1Visa.lean`).  
- Theorems are overwhelmingly definitional. Many are `rfl`/`simp`/`decide` and test code paths rather than legal properties.  
- The paper’s theorem count is inconsistent. The code in the provided files yields 39 theorems (15 IRC + 13 O‑1 + 11 TCP), not 44. That is basic sloppiness.  
- The comparison table assigns perfect scores to LegalLean while the code fails to implement those dimensions in any substantive sense.

Honesty about limitations feels performative. The paper admits the `sorry` loophole and “no temporal algebra,” yet still scores itself 5/5 for “machine‑checkable guarantees” and “temporal reasoning.” The self‑assessment contradicts the actual implementation.

**Q8. Single most important improvement**  
Replace the hand‑coded decision procedures with a **verified defeasible inference engine** that consumes `LegalRule` + `Defeats` and produces `FormalisationBoundary P` for *specific propositions* `P`, with proofs for `formal`. This change would force the claimed verification to exist and would make the case studies about legal reasoning rather than about an ad‑hoc `if` tree.

---

If you want, I can sketch what the minimal defeasible semantics and the corrected `FormalisationBoundary` type would look like in Lean, but that’s beyond what this submission currently shows.

---
Completed: Mon Mar 16 19:52:52 UTC 2026
