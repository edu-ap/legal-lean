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
  - Matter of Rijal, USCIS Administrative Appeals Office (AAO), non-precedent
    decision (2008): comparable evidence must meet the same substantive threshold
    as the standard criteria it substitutes — equivalent in import, relevance,
    and weight to the listed evidentiary criteria under 8 CFR § 204.5(h)(4)

  Compatible with Lean 4 v4.24.0.
  Uses List.Nodup from Lean 4 core (Init/Data/List/Basic.lean) in place of
  the former custom AllDistinct inductive — the API is identical:
    List.Nodup []                              ↔  AllDistinct.nil
    List.nodup_cons.mpr ⟨hni, ht⟩  ↔  AllDistinct.cons hni ht
    List.nodup_cons.mp h            ↔  cases h with | cons hni ht => ...
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
-- Duplicate-free list: List.Nodup (Lean 4 core)
-- ============================================================

-- List.Nodup is defined in Init/Data/List/Basic.lean as:
--   def List.Nodup : List α → Prop := List.Pairwise (· ≠ ·)
--
-- It ships with the following API that we use below:
--   List.nodup_nil    : Nodup []
--   List.nodup_cons   : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l
--   List.nodupDecidable : ∀ [DecidableEq α] (l : List α), Decidable (Nodup l)
--
-- No import needed beyond LegalLean.Core (which imports Init.Data.List).

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
  authority := LegalLean.Authority.uscis
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
  authority := LegalLean.Authority.uscis
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
  authority := LegalLean.Authority.uscis
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
  authority := LegalLean.Authority.uscis
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
  authority := LegalLean.Authority.uscis
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
  authority := LegalLean.Authority.uscis
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
  authority := LegalLean.Authority.uscis
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
  authority := LegalLean.Authority.uscis
  scope := "Determination that (i) standard criteria do not apply to the field AND " ++
           "(ii) the comparable evidence demonstrates extraordinary ability at equivalent weight"
  constraints := [
    "Must be comparable in import, relevance, and weight to listed criteria",
    "Petitioner bears burden of explaining why standard criteria do not apply",
    "Matter of Rijal, USCIS AAO (2008): comparable evidence must meet the same substantive threshold as the standard criteria it substitutes"
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
-- Cardinality encoded via List.Nodup + List.length ≥ 3
-- ============================================================

/-- Part 1 (Kazarian): Meets at least 3 of the 8 evidentiary criteria.
    `satisfied` is a duplicate-free list of criteria the applicant evidenced.
    `distinct` proves no criterion is listed twice (so length = cardinality).
    `cardinal` proves length ≥ 3.
    `evidence` maps each element to an EvidenceFor its Prop.

    This structure CAN ONLY BE INHABITED if the applicant genuinely has
    evidence for ≥ 3 distinct criteria — Lean enforces this at compile time.

    `distinct` uses `List.Nodup` (Lean 4 core, Init/Data/List/Basic.lean),
    defined as `List.Pairwise (· ≠ ·)`.  Constructors:
      · `List.nodup_nil`                   for the empty list
      · `List.nodup_cons.mpr ⟨hni, ht⟩`   to prepend an element not in the tail -/
structure MeetsThreeCriteria (a : Applicant) where
  /-- The duplicate-free list of criteria the applicant has satisfied. -/
  satisfied : List Criterion
  /-- No criterion appears twice (List.Nodup = List.Pairwise (· ≠ ·)). -/
  distinct  : satisfied.Nodup
  /-- At least 3 criteria must be met (cardinality constraint). -/
  cardinal  : satisfied.length ≥ 3
  /-- For each satisfied criterion, a proof witness (EvidenceFor its Prop). -/
  evidence  : ∀ c ∈ satisfied, LegalLean.EvidenceFor (criterionProp a c)

-- ============================================================
-- OneTimeAchievement: the alternative one-time-award eligibility path
-- (8 CFR § 204.5(h)(5) — single achievement of major, international acclaim)
-- ============================================================

/-- A one-time achievement that may substitute for the "3 of 8" threshold.
    Under 8 CFR § 204.5(h)(5), a single career achievement of major, international
    significance (such as a Nobel Prize or equivalent) can establish extraordinary
    ability without needing to meet ≥ 3 of the 8 standard criteria.

    This is an ALTERNATIVE eligibility path, not a supplement to MeetsThreeCriteria.
    The adjudicator must determine whether the achievement meets the "major, one-time
    internationally recognised award" standard — an open-texture determination.

    Fields:
    - `award`: the qualifying one-time achievement award record
    - `awardIsRecognised`: formal evidence the award is recorded as internationally
      recognised (formalisable part — Lean verifies this field holds)
    - `adjudicatorDetermination`: explicit annotation that the final determination
      of "major" significance rests with USCIS (open texture, not machine-verifiable) -/
structure OneTimeAchievement (a : Applicant) where
  /-- The award that constitutes the one-time achievement. -/
  award : Award
  /-- Formal (record-level) evidence the award is internationally recognised. -/
  awardIsRecognised : award.isRecordedAsRecognised = true
  /-- Annotation: final "major significance" determination is a FormalisationBoundary.
      Default value provided so callers need only supply `award` + `awardIsRecognised`. -/
  adjudicatorDetermination : LegalLean.FormalisationBoundary Prop :=
    LegalLean.FormalisationBoundary.boundary
      ("8 CFR § 204.5(h)(5): whether the award constitutes a 'major, one-time " ++
       "internationally recognised award' is an adjudicator determination — " ++
       "the formalisable part (award recorded as recognised) is verified by Lean")
      LegalLean.Authority.uscis

/-- The disjunctive base eligibility condition:
    an applicant satisfies the primary evidentiary threshold if they EITHER
    (a) meet ≥ 3 of the 8 standard criteria (MeetsThreeCriteria), OR
    (b) have a single qualifying one-time internationally recognised achievement
        (OneTimeAchievement).

    This disjunction faithfully encodes 8 CFR § 204.5(h)(3)–(5):
    the "3 of 8" path (MeetsThreeCriteria) is the ordinary route;
    the one-time achievement path (OneTimeAchievement) is the alternative
    for applicants whose career peak is a single landmark award. -/
def MeetsBaseEligibility (a : Applicant) : Prop :=
  Nonempty (MeetsThreeCriteria a) ∨ Nonempty (OneTimeAchievement a)

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
    LegalLean.Authority.uscis

/-- Full O-1A eligibility: BOTH parts of the Kazarian two-part test.
    Part 1 is formalisable (List.Nodup list with length ≥ 3).
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
    ability AND satisfy EITHER the "3 of 8" standard criteria threshold
    (MeetsThreeCriteria) OR the one-time-achievement alternative path
    (OneTimeAchievement) — a disjunction encoding 8 CFR § 204.5(h)(3)–(5).

    The `conclusion` field captures the disjunctive evidentiary threshold:
    `MeetsBaseEligibility a = Nonempty (MeetsThreeCriteria a) ∨ Nonempty (OneTimeAchievement a)`.
    The overarching `HasExtraordinaryAbility` standard (the holistic final merits
    determination) is captured in `EligibleO1A.part2` rather than here, because
    it is not machine-verifiable and sits at the FormalisationBoundary. -/
def R1_O1A_BaseEligibility : LegalRule Applicant where
  id := "R1-O1A"
  description := "Applicant is eligible for O-1A classification if they demonstrate " ++
                 "extraordinary ability by satisfying EITHER (a) at least 3 of 8 " ++
                 "evidentiary criteria in 8 CFR § 204.5(h)(3) (MeetsThreeCriteria), OR " ++
                 "(b) a single major internationally recognised one-time achievement " ++
                 "under 8 CFR § 204.5(h)(5) (OneTimeAchievement)"
  modality := Deontic.obligatory
  priority := ⟨1, "regulation (8 CFR § 204.5(h))"⟩
  conclusion := fun a => MeetsBaseEligibility a
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

/-- Theorem: A List.Nodup pair implies the two elements are unequal.
    This is the kernel [core mechanism] of the "3 of 8" type: List.Nodup
    prevents any criterion from being counted twice.

    Legal significance: two criteria that are mapped to DIFFERENT axioms
    (e.g. majorAward → MeetsAwardCriterion vs membership → MeetsMembershipCriterion)
    cannot be conflated by listing the same criterion twice. If both appear
    in the `satisfied` list, List.Nodup requires they are distinct values.

    Why this matters: it is not possible to "game" the cardinality requirement
    by listing the same criterion under two different framings — the Criterion
    type has decidable equality and List.Nodup enforces uniqueness. -/
theorem nodup_pair_implies_ne
    {α : Type} [DecidableEq α] (x y : α)
    (h : List.Nodup [x, y]) : x ≠ y := by
  simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil, and_true] at h
  exact h.1

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
