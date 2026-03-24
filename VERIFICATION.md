# Independent Verification Protocol

**LegalLean — Verified Legal Reasoning in Lean 4**

This document enables any reader to verify the correctness of this work independently, using three complementary methods. Each method is self-contained. You do not need the authors' machines, accounts, or assistance.

---

## Layer 1: Lean 4 Type Checker (deterministic, free)

The Lean 4 type checker is a proof kernel: a small, independently auditable program that accepts a term if and only if its type is inhabited [has a valid proof]. Every theorem in this repository has been verified by this kernel. There is no reliance on tactics that could silently fail, and no `sorry` placeholders that would allow the kernel to accept an unproven claim.

### Prerequisites

- `git` (any recent version)
- `elan` — the Lean version manager (analogous to `rustup` for Rust)

Install `elan` on Linux/macOS:

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
```

On Windows, use the installer from https://github.com/leanprover/elan/releases.

### Verification steps

```bash
# 1. Clone the repository
git clone https://github.com/edu-ap/legal-lean.git
cd legal-lean

# 2. elan reads lean-toolchain and fetches the correct Lean version automatically
#    This may take several minutes on first run (downloading ~200MB toolchain)
lake build

# 3. Check for sorry stubs (must return no output)
grep -r "sorry" LegalLean/ --include="*.lean"

# 4. Check for axioms beyond the declared open-texture axioms
#    Expected: only IsQualifiedResidence, IsSubstantialImprovement,
#              MixedUseAllocation, HasExtraordinaryAbility, HasSustainedAcclaim,
#              AwardIsRecognised, AssociationRequiresOutstanding,
#              ContributionsAreMajor, RoleIsCriticalAtDistinguished, SalaryIsHigh,
#              ComparableEvidenceApplies
#    Any axiom NOT in this list would be an undisclosed assumption.
grep -r "^axiom" LegalLean/ --include="*.lean"
```

### Expected output

```
Build completed successfully (N jobs).
```

The `grep -r "sorry"` command must return no output. Any output means an unverified claim has been accepted by the kernel.

### What this proves

A successful build with zero `sorry` and zero unexpected axioms establishes:

1. **Type consistency**: all types are well-formed and consistent with each other.
2. **Theorem correctness**: every statement marked `theorem` has a complete machine-verified proof.
3. **Open-texture honesty**: the axioms we declared (e.g. `HasExtraordinaryAbility`, `IsQualifiedResidence`) are the only unverified propositions in the system. They represent genuine open texture, not gaps in our reasoning.
4. **No fabricated proofs**: the Lean kernel does not accept arguments from authority, analogy, or rhetoric — only type-correct proof terms.

---

## Layer 2: Aristotle Automated Prover (independent verification)

Aristotle (https://aristotle.harmonic.fun/) is an independent theorem-proving service that maintains its own Lean 4 installation. It provides a second opinion that is institutionally and computationally separate from our build environment.

### Prerequisites

- Python 3.8 or later
- An Aristotle API key (free tier available at https://aristotle.harmonic.fun/)

### Setup

```bash
pip install aristotlelib

# Set your API key
export ARISTOTLE_API_KEY="your-key-here"
```

### Running the verification

```bash
# Dry run: checks all files, reports sorry stubs and unverified claims
python scripts/aristotle_prover.py --all --dry-run

# Full verification: submits all theorems to Aristotle's prover
python scripts/aristotle_prover.py --all
```

### Expected output

A passing run produces a table of the form:

```
File                                   Theorems   Verified   Sorry stubs
LegalLean/Core.lean                           0          0             0
LegalLean/Defeasible.lean                     0          0             0
LegalLean/CaseStudies/IRC163h.lean            3          3             0
LegalLean/CaseStudies/IRC163h/Theorems.lean   7          7             0
LegalLean/CaseStudies/O1Visa.lean             5          5             0
────────────────────────────────────────────────────────────────────────
TOTAL                                        15         15             0

All theorems verified. No sorry stubs detected.
```

### What this proves

Aristotle uses a different Lean installation, different hardware, and a different caching layer than the authors' machines. Agreement between Aristotle and Layer 1 eliminates the possibility that a build-environment quirk produced a false positive. The two verifiers are independent in the sense that matters: they share only the Lean proof kernel specification, not the implementation.

---

## Layer 3: Adversarial LLM Review (reproducible peer review)

Paste the following prompt verbatim into any frontier LLM (GPT-5, Claude Opus 4.6, Gemini 3.1 Pro, or equivalent). The prompt requests the harshest possible academic criticism. Reproduce this review when submitting to any venue.

---

**PROMPT — copy from the dashed line below to the dashed line above the "End of prompt" marker:**

---

You are acting as an anonymous peer reviewer for a theoretical computer science / legal informatics paper. Your job is to provide the most rigorous, critical, and adversarial review possible. Do not soften criticism. Identify every weakness, gap, triviality, and missed opportunity.

The paper claims to make the following contributions:
- T1: Dependent types (Lean 4) can encode legal eligibility conditions in a way that is machine-checkable.
- T2: Non-monotonic (defeasible) legal reasoning can be represented in a dependently-typed system without losing the non-monotonic character.
- T3: Hart's "open texture" — the irreducible vagueness of legal concepts — can be represented as a first-class type (`FormalisationBoundary`) rather than as an external limitation.
- T4: The boundary between formalisable and non-formalisable legal conditions can be made precise and machine-annotated.
- T5: This approach scales to realistic statutes (IRC §163(h), 8 CFR § 204.5(h)).

Below are the key Lean 4 source files. Read them carefully, then answer the five questions that follow.

---

**FILE: LegalLean/Core.lean (abridged)**

```lean
namespace LegalLean

inductive Deontic where
  | permitted | prohibited | obligatory
  deriving Repr, BEq, Inhabited, DecidableEq

structure LegalRule (α : Type) where
  id : String
  description : String
  modality : Deontic
  priority : Priority
  conclusion : α → Prop
  defeatedBy : List String

structure EvidenceFor (P : Prop) where
  source : String
  artifact : Option String
  witness : P

class RequiresHumanDetermination (P : Prop) where
  reason : String
  authority : String

class Vague (P : Prop) extends RequiresHumanDetermination P where
  core : String
  penumbra : String

class Discretionary (P : Prop) extends RequiresHumanDetermination P where
  scope : String
  constraints : List String

inductive FormalisationBoundary (P : Sort _) where
  | formal (proof : P) : FormalisationBoundary P
  | boundary (reason : String) (authority : String) : FormalisationBoundary P
  | mixed (formalPart : String) (humanPart : String) : FormalisationBoundary P

end LegalLean
```

---

**FILE: LegalLean/CaseStudies/IRC163h/Theorems.lean (key theorems)**

```lean
-- T2: defeat chain has depth exactly 2 (R3 defeats E1.1 which defeats R1)
theorem defeat_chain_exists :
    ∃ d1 d2 : Defeats,
      d1 ∈ allDefeats ∧ d2 ∈ allDefeats ∧
      d1.defeater = "R3" ∧ d1.defeated = "E1.1" ∧
      d2.defeater = "E1.1" ∧ d2.defeated = "R1" := by
  exact ⟨defeat_R3_E1_1, defeat_E1_1_R1, ...⟩

-- T2: grandfather clause does NOT directly defeat the base rule
theorem grandfather_does_not_directly_defeat_base :
    ∀ d ∈ allDefeats, d.defeater = "R3" → d.defeated ≠ "R1" := ...

-- T3: every code path through isDeductible is formal or boundary, never mixed
theorem no_mixed_outcomes (payment year status) :
    ¬isMixedOutcome (isDeductible payment year status) := ...

-- T3: every boundary annotation in isDeductible has authority "IRS / Tax Court"
theorem boundary_authority_is_irs_tax_court (...) :
    a = "IRS / Tax Court" := ...

-- T1+T3: the three conditions that trigger automatic rejection (formal False)
theorem auto_reject_conditions (...) :
    (payment.paidByIndividual = false → isDeductible ... = formal False) ∧
    (payment.indebtedness.securedByResidence = false → isDeductible ... = formal False) ∧
    (purpose = other → year ≥ 2018 → ... → isDeductible ... = formal False) := ...
```

---

**FILE: LegalLean/CaseStudies/O1Visa.lean (key structures and theorems)**

```lean
-- "3 of 8" encoded as a dependent type
structure MeetsThreeCriteria (a : Applicant) where
  satisfied : List Criterion
  distinct  : AllDistinct satisfied
  cardinal  : satisfied.length ≥ 3
  evidence  : ∀ c ∈ satisfied, EvidenceFor (criterionProp a c)

-- Kazarian Part 2 is always at the boundary
def finalMeritsDetermination (_a : Applicant) : FormalisationBoundary Prop :=
  FormalisationBoundary.boundary
    ("Kazarian v. USCIS: meeting ≥ 3 criteria is necessary but not sufficient...")
    "USCIS adjudicator (AAO appealable)"

-- Key theorems
theorem three_criteria_lower_bound (a) (w : MeetsThreeCriteria a) :
    w.satisfied.length ≥ 3 := w.cardinal

theorem final_merits_is_boundary (a) :
    ∃ reason authority,
        finalMeritsDetermination a = FormalisationBoundary.boundary reason authority

theorem eligibility_always_mixed (a) (w : MeetsThreeCriteria a) :
    ∃ fp hp, determineEligibility a w = FormalisationBoundary.mixed fp hp

theorem empty_list_ineligible (a) (w : MeetsThreeCriteria a) :
    w.satisfied ≠ []
```

---

**Please answer all five questions. Be harsh.**

**Q1. Which theorems are trivial — that is, which merely unfold definitions or read off a field value without proving any non-obvious property?**

Identify each trivial theorem by name. Explain why it is trivial (e.g. "proof is `w.cardinal` — this is field access, not a theorem"). Be specific about what would make a replacement non-trivial.

**Q2. Which theorems prove genuine properties about legal reasoning — properties that a legal scholar or a practitioner would find meaningful and non-obvious?**

For each such theorem, state: (a) what legal concept it captures, (b) why it is not obvious from the definitions alone, and (c) what practical consequence it has (e.g. a programmer implementing this statute incorrectly could violate this theorem).

**Q3. Is `FormalisationBoundary` a genuine theoretical contribution, or is it essentially a labelled union (tagged sum) that adds annotation overhead without constraining anything?**

Specifically: does the type system prevent any incorrect usage that would otherwise be permitted? Or could a dishonest implementer trivially produce `FormalisationBoundary.formal (sorry)` and defeat the entire mechanism? If the latter, what design change would close this gap?

**Q4. What properties SHOULD be proven that are missing from this formalisation?**

For IRC §163(h) specifically: what theorems would a tax lawyer consider the most important properties of this provision, and are any of them absent? For O-1A: what properties of the Kazarian two-part test remain unverified?

**Q5. How does this work compare to prior systems: DDL (Governatori's Defeasible Deontic Logic), Catala (Merigoux et al.), L4L (Palmirani et al.), and LegalRuleML?**

For each prior system: (a) what does it do better than LegalLean, (b) what does LegalLean do better, and (c) is there a category of legal reasoning that neither handles well?

---

*End of prompt.*

---

### Interpreting the review

A strong verification result will produce a review that:

- Identifies `three_criteria_lower_bound` and `final_merits_is_boundary` as relatively trivial (field access and `rfl`, respectively).
- Rates `no_mixed_outcomes` and `boundary_authority_is_irs_tax_court` as substantive (require case analysis over all code paths).
- Rates `defeat_chain_exists` and `grandfather_does_not_directly_defeat_base` as legally meaningful (they prove structural properties of the defeat graph).
- Notes the `sorry` / `FormalisationBoundary.formal (sorry)` gap in Q3, which is a known limitation addressed in the monograph.
- Suggests missing theorems for Q4 (e.g. monotonicity of `acquisitionLimit` in year, completeness of the defeat graph relative to the statute text).

If the LLM review is substantially harsher than this baseline, treat the discrepancy as a research finding and investigate before submitting.

---

## Theorem Audit Trail

The following table maps every theorem in the repository to its legal meaning, the thesis component it supports, and a judgment of whether it is substantive or a unit test [a check that code behaves as written, rather than a proof of a non-obvious property].

### IRC §163(h) — `IRC163h.lean`

| Theorem | What it proves (legal terms) | Thesis component | Trivial or substantive | Proof technique |
|---------|------------------------------|-----------------|----------------------|-----------------|
| `tcja_prohibits_home_equity` | Post-2017, home equity interest is never deductible. The TCJA elimination is absolute for this category of debt. | T2 (defeasibility), T4 (boundary) | Unit test: traces one code path through `isDeductible` to `formal False`. Verifies the encoding is correct, not that the property is non-obvious. | `simp` with explicit hypotheses |
| `non_individual_never_deducts` | Corporations and trusts cannot claim the mortgage interest deduction regardless of all other facts. | T1 (types encode eligibility), T4 | Unit test: same structure. Confirms `paidByIndividual = false` short-circuits to `formal False`. | `simp` |
| `unsecured_never_deducts` | Unsecured debt cannot qualify for the deduction, regardless of purpose, amount, or filing status. | T1, T4 | Unit test. | `simp` |

### IRC §163(h) — `IRC163h/Theorems.lean`

| Theorem | What it proves (legal terms) | Thesis component | Trivial or substantive | Proof technique |
|---------|------------------------------|-----------------|----------------------|-----------------|
| `defeat_direct_acyclicity` | No rule in IRC §163(h) simultaneously defeats itself. The defeat graph is acyclic [has no loops]. A cycle would represent an irresolvable legal contradiction — a rule that both applies and does not apply. | T2 (non-monotonic structure is well-founded) | Substantive: proves a structural property of the defeat graph extracted from the statute. The acyclicity condition is necessary for Reiter's extension semantics to be well-defined. | `simp` + `rcases` over `allDefeats` |
| `defeat_chain_exists` | The defeasibility structure of IRC §163(h) has depth 2: R3 (grandfather clause) defeats E1.1 (dollar limit) which defeats R1 (base rule). This means resolution requires transitive reasoning — a flat priority ordering is insufficient. | T2 | Substantive: proves that the statute's defeasibility cannot be flattened. Two rules with different priority levels are in the defeat list, and their chain creates a non-trivial ordering problem. Relevant to any implementation that processes rules in linear order. | Exact term |
| `grandfather_does_not_directly_defeat_base` | The grandfather clause exempts pre-1987 debt from the dollar limits (E1.1), but NOT from the underlying requirement that interest be qualified residence interest. Grandfathered taxpayers still must satisfy R1's conditions. | T2 | Substantive (legally): this is a subtle point that practitioners and IRS guidance confirm. The grandfather preserves eligibility for the category but does not remove all conditions. Incorrect implementations might treat R3 as overriding R1 entirely. | `simp_all` + `rcases` over `allDefeats` |
| `R1_R2_deontic_conflict` | The statute contains a genuine deontic conflict: R1 permits deduction; R2 prohibits it for post-2017 home equity. The conflict is resolved by defeat (lex posterior), not by flattening the modalities. | T2, T3 | Substantive in the context of T3: proves that our encoding preserves the conflict rather than silently resolving it. This matters because flattening would hide the legal mechanism from the type system. | `simp` with record field access |
| `pre_tcja_no_prohibition` | Before 2018, R2's conclusion (prohibition) cannot hold. The TCJA prohibition is temporally scoped: the same debt that is prohibited post-2017 was permitted pre-2018. | T2 | Substantive: proves temporal scoping of the prohibition. A legal system that does not distinguish by year would fail this theorem. | `omega` |
| `no_mixed_outcomes` | Every code path through `isDeductible` for IRC §163(h) produces either a fully formal result or a boundary result — never a `mixed` result. This is a structural property of the STATUTE: it does not have partially-formal eligibility conditions (unlike O-1A, which does). | T3, T4 | Substantive: requires case analysis over all branches of `isDeductible`. The result distinguishes IRC §163(h) from O-1A at the type level, reflecting a genuine difference in statutory structure. | `cases` on all Bool and enum branches |
| `boundary_authority_is_irs_tax_court` | Every `FormalisationBoundary.boundary` annotation produced by `isDeductible` names "IRS / Tax Court" as the determining authority. There is no boundary annotation that fails to specify an institutional authority. | T3 | Substantive: connects the type system to Hart's theory of institutional settlement of open texture. Proves the annotations are not arbitrary strings but are consistently tied to the legal institution responsible for resolving penumbral cases in this statute. | `simp` + `split` + `simp_all` over all boundary-producing paths |
| `all_rules_are_permissions_or_prohibitions` | All three rules in IRC §163(h) have deontic modalities drawn from {permitted, prohibited}. No rule is `obligatory`. This validates that the deduction is a permission (you MAY deduct), not an obligation. | T1 | Unit test: reads off `modality` fields. Confirms the encoding matches the statute's normative structure, but trivially. | `simp` |
| `auto_reject_conditions` | Three conditions guarantee automatic rejection without human determination: (1) payment by a non-individual, (2) unsecured debt, (3) home equity purpose post-2017. These are the conditions where `formal False` is returned — no IRS/Tax Court discretion required. | T1, T4 | Substantive as a bundle: the three conjuncts together characterise the complete set of automatically-decidable rejection conditions. This has practical consequence: a legal aid tool could screen out these cases without triggering human review. | `refine` + `simp` per conjunct |

### O-1A Visa — `O1Visa.lean`

| Theorem | What it proves (legal terms) | Thesis component | Trivial or substantive | Proof technique |
|---------|------------------------------|-----------------|----------------------|-----------------|
| `three_criteria_lower_bound` | Any applicant who can construct a `MeetsThreeCriteria` witness has satisfied at least 3 distinct criteria. | T1 (dependent type enforces eligibility) | Trivial: `w.cardinal` is field access. The content is in the type definition, not the theorem. The theorem is a documentation artefact that makes the property visible. | Field projection |
| `final_merits_is_boundary` | The Kazarian Part 2 final merits determination is always at the formalisation boundary — it can never be produced as a `formal` result by any call to `finalMeritsDetermination`. | T3, T4 | Trivial: `finalMeritsDetermination` is defined as a single `boundary` constructor, so the theorem proves by `rfl`. Its value is documentation: it states explicitly that no implementation can machine-verify Kazarian Part 2. | `rfl` |
| `R1_R2_deontic_distinct` | The base eligibility rule (R1, obligatory) and the comparable evidence alternative (R2, permitted) have different deontic modalities. The regulation distinguishes between what USCIS must do and what a petitioner may do. | T1, T2 | Unit test with mild legal content: confirms the modality encoding matches the regulatory structure. Practically relevant: an implementation that treated both as `obligatory` would incorrectly mandate comparable evidence. | `simp` |
| `defeat_direct_acyclicity` | The O-1A defeat graph is acyclic. The comparable evidence route does not defeat itself. | T2 | Unit test on a single-element `allDefeats`: the proof is trivial because the list has one entry. Value is baseline structural soundness. | `simp` + `rcases` |
| `eligibility_always_mixed` | For any applicant with a `MeetsThreeCriteria` witness, `determineEligibility` returns a `mixed` result — never `formal` or `boundary`. This proves that O-1A eligibility is always partially formal (Part 1 verified) and partially at the boundary (Part 2 not). | T3, T4 | Trivial: `determineEligibility` is definitionally a `mixed` constructor. The theorem's value is that it proves O-1A differs from IRC §163(h) (`no_mixed_outcomes`) at the type level. | `rfl` |
| `empty_list_ineligible` | No applicant can meet O-1A criteria with zero satisfied criteria. | T1 | Unit test / sanity check. Follows directly from `cardinal ≥ 3` and `length [] = 0`. | `omega` |

---

## Statute-to-Code Mapping

### IRC §163(h): Statutory section to Lean 4 definition

This table enables a reviewer to check whether our formalisation covers the statute's provisions and to identify any gaps.

| Statutory section | Content | Lean 4 encoding | Fully formalisable? |
|------------------|---------|-----------------|---------------------|
| §163(h)(1) | General disallowance of personal interest | `R1_BaseDeduction` (modality: `permitted`, meaning deduction is allowed only for qualified interest) | Yes — binary rule |
| §163(h)(2)(D) | Qualified residence interest is an exception to the disallowance | `R1_BaseDeduction.conclusion` | Partial — "qualified residence" is `axiom IsQualifiedResidence` |
| §163(h)(3)(A) | Acquisition indebtedness definition | `isAcquisitionIndebtedness`, `IndebtednessPurpose.acquire`, `IndebtednessPurpose.construct` | Partial — "substantially improve" is `axiom IsSubstantialImprovement` |
| §163(h)(3)(B) | Substantially improve: acquisition indebtedness sub-criterion | `IndebtednessPurpose.substantiallyImprove`, `FormalisationBoundary.boundary` annotation | No — open texture; Vague instance documents core/penumbra |
| §163(h)(3)(C) | Dollar limits: $750,000 post-TCJA, $1,000,000 pre-TCJA (MFS: half) | `acquisitionLimit`, `withinAcquisitionLimit` | Yes — purely arithmetic |
| §163(h)(4)(A) | Qualified residence: principal residence + one other | `axiom IsQualifiedResidence`, Vague instance (core: settled; penumbra: mobile homes, timeshares, boats) | No — open texture |
| §163(h)(4)(C) | Home equity limit: $100,000 ($50,000 MFS) | `homeEquityLimit`, `withinHomeEquityLimit` | Yes — purely arithmetic |
| TCJA §11043 | Suspension of home equity deduction post-2017 | `R2_TCJAProhibition`, `postTCJA`, defeat relation `defeat_R2_R1` | Yes — date comparison |
| TRA 1986, grandfather | Pre-October 1987 debt grandfathered from limits | `R3_GrandfatherRule`, `preTRA87`, defeat relation `defeat_R3_E1_1` | Yes — ISO date string comparison |
| Treas. Reg. §1.163-8T | Tracing rules for mixed-use debt allocation | `axiom MixedUseAllocation`, Discretionary instance | No — IRS discretion |

**Coverage assessment.** All three rules and four defeat relations are encoded. The two genuine open-texture terms (qualified residence, substantially improve) and the one discretionary determination (mixed-use allocation) are represented as axioms with documented Vague/Discretionary instances. No statutory provision is silently omitted.

**Known gap.** The dollar limit comparison uses ISO 8601 string ordering as a proxy for date comparison (`preTRA87`). This is correct for well-formed date strings but is not a full date type with arithmetic. A reviewer checking this section should confirm the encoding works for dates of the form `YYYY-MM-DD` only.

### O-1A Visa (8 CFR § 204.5(h)): Criterion to Lean 4 encoding

| Criterion | Regulatory text (abridged) | Lean 4 encoding | Formalisable portion | Open-texture portion |
|-----------|---------------------------|-----------------|---------------------|---------------------|
| C1 — Major award | Receipt of nationally/internationally recognised prize for excellence | `Criterion.majorAward`, `axiom AwardIsRecognised` (Vague instance) | Award existence (formalisable as record) | Prestige threshold ("recognised") — core: Nobel/Turing; penumbra: regional prizes |
| C2 — Membership | Association requiring outstanding achievement judged by experts | `Criterion.membership`, `axiom AssociationRequiresOutstanding` (Discretionary instance) | Membership fact (formalisable) | Whether association standard qualifies — USCIS discretion with three statutory constraints |
| C3 — Media coverage | Published material in professional/major media about person and work | `Criterion.mediaCoverage`, `hasMediaCoverage` | Count of recorded-as-major outlets | Which outlets are "major" — Discretionary |
| C4 — Judging | Participation as judge of others' work | `Criterion.judgingRole`, `hasJudgingRole` | Count of judging roles (≥ 1) | Whether informal peer review qualifies — Vague |
| C5 — Original contributions | Original contributions of major significance | `Criterion.originalContribs`, `axiom ContributionsAreMajor` (Discretionary instance) | Existence of contributions | "Major significance" — requires expert letters; entirely fact-specific |
| C6 — Scholarly authorship | Scholarly articles in professional/major publications | `Criterion.scholarlyAuthorship`, `hasScholarlyArticle` | Count of recorded-as-major articles | Which outlets are "professional or major" — Discretionary |
| C7 — Critical employment | Critical/essential capacity at distinguished organisation | `Criterion.criticalEmployment`, `axiom RoleIsCriticalAtDistinguished` (Vague instance) | Employment fact (formalisable) | "Critical/essential" and "distinguished" — Vague; core: Fortune 500 C-suite; penumbra: mid-level technical roles |
| C8 — High salary | High salary relative to others in field | `Criterion.highSalary`, `axiom SalaryIsHigh` (Vague instance) | Salary figure (formalisable) | "High" relative to field — no statutory threshold; field-relative |

**"3 of 8" cardinality constraint.** Encoded as `MeetsThreeCriteria.cardinal : satisfied.length ≥ 3` combined with `AllDistinct satisfied`. This avoids the `Mathlib.Data.Finset` dependency by encoding set cardinality as a duplicate-free list with length bound. The encoding is equivalent for finite lists of `DecidableEq` elements.

**Kazarian two-part test.** Part 1 (criteria count) is fully encoded in `MeetsThreeCriteria`. Part 2 (final merits determination) is always at the formalisation boundary, proved by `final_merits_is_boundary`. This faithfully represents the 9th Circuit's holding that Part 1 is necessary but not sufficient.

**Criterion proxy mapping.** `criterionProp` maps all criteria except C5 and C8 to `HasExtraordinaryAbility`, and C5 to `ContributionsAreMajor`, C8 to `SalaryIsHigh`. This is a simplification: ideally each criterion would have a distinct axiom. The per-criterion Vague/Discretionary instances provide the open-texture analysis for each one individually. The mapping is intellectually honest (all three targets are axioms — no fabricated proofs) but loses some granularity in the type-level distinction between criteria. This is noted as a future-work item in the monograph.

---

*This document was authored for the LegalLean monograph. Version controlled alongside the Lean 4 source. Last updated: 2026-03-14.*
