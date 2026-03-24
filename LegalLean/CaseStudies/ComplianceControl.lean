/-
  LegalLean.CaseStudies.ComplianceControl — Migrating an OpenCompliance
  Boolean control to LegalLean types.

  Context: Eduardo is the author of both LegalLean and OpenCompliance.
  OpenCompliance uses Boolean predicates for InfoSec compliance controls
  (ISO 27001 / SOC 2 Type II). This case study demonstrates that LegalLean's
  type system — FormalisationBoundary, LegalRule, Defeats — generalises to
  this domain without modification.

  Control chosen: MFA / identity access management (ISO 27001 A.9.4.2 /
  SOC 2 CC6.1). This is the simplest possible InfoSec control and therefore
  the clearest vehicle for showing the migration pattern.

  Migration pattern (three steps):
    1. Boolean predicate  →  LegalRule with FormalisationBoundary conclusion
    2. Risk acceptance    →  Defeats relation (higher-priority rule defeats gap)
    3. Training attestation →  RequiresHumanDetermination / boundary

  Key insight: OpenCompliance's Boolean predicates are a special case of
  FormalisationBoundary.formal — they capture only the formalisable fragment
  of each control. LegalLean makes the boundary between formalisable and
  human-determinable explicit in the type, so auditors can see exactly where
  machine verification stops.

  Authority mapping (ISO 27001 vs LegalLean.Authority):
    Authority.accc is used as a proxy for the external certification body
    (BSI / Bureau Veritas / etc.) throughout.  A production deployment would
    extend the Authority inductive with InfoSec-specific constructors; for this
    case study we re-use the existing closed enum and document the mapping here.

  Source: ISO/IEC 27001:2022 Annex A, control A.8.5 (formerly A.9.4.2);
          AICPA Trust Services Criteria CC6.1 (2017 update).

  Compatible with Lean 4 v4.24.0.  Uses LegalLean.Core and LegalLean.Defeasible.
  No Mathlib. No Float.
-/

import LegalLean.Core
import LegalLean.Defeasible

namespace LegalLean.CaseStudies.ComplianceControl

-- ============================================================
-- PART 0: Original OpenCompliance approach (Boolean predicates)
-- Retained as comments for direct comparison.
-- ============================================================

/-
  The original OpenCompliance encoding:

  structure IdentityEvidence where
    mfaRequired : Bool
    conditionalAccessEnabled : Bool

  def AdministrativeMfaSatisfied (e : IdentityEvidence) : Prop :=
    e.mfaRequired = true ∧ e.conditionalAccessEnabled = true

  Problems with Boolean predicates alone:
  1. No boundary annotation: "appropriate MFA" is vague (TOTP vs hardware key
     vs SMS OTP all satisfy the Boolean, but their risk profiles differ wildly).
  2. No defeasibility: a Board-approved risk acceptance can legitimise a control
     gap, but this has no representation in the Boolean model.
  3. No human-determination flag: ISO 27001 uses "appropriate", "reasonable", and
     "adequate" throughout. Boolean predicates silently erase these vague terms.
  4. No priority: when a compensating control partially satisfies a gap, there is
     no way to express that it overrides the primary-control failure.
-/

-- ============================================================
-- PART 1: Domain types for the MFA/identity control
-- ============================================================

/-- Evidence record for an identity access management (IAM) control assessment.
    Carries the raw evidence fields that feed into control evaluation.

    This is the direct counterpart of OpenCompliance's IdentityEvidence.  The
    Boolean fields are preserved — LegalLean does not discard formalisable
    evidence, it AUGMENTS it with boundary annotations. -/
structure IamEvidence where
  /-- MFA is configured as required for privileged accounts. -/
  mfaRequired : Bool
  /-- Conditional-access policies enforcing MFA are enabled. -/
  conditionalAccessEnabled : Bool
  /-- Board or CISO has issued a time-boxed risk acceptance for this control. -/
  riskAcceptanceOnFile : Bool
  /-- A training attestation record exists (completed by affected personnel). -/
  trainingAttestationExists : Bool
  /-- Free-text description of the MFA mechanism deployed (e.g. "TOTP", "FIDO2"). -/
  mfaMechanism : String
  deriving Repr

-- ============================================================
-- PART 2: The formalisable fragment (Boolean predicates)
-- These are the conditions LegalLean can verify without human input.
-- ============================================================

/-- The formalisable core of the MFA control: both flags are set.
    This is identical to OpenCompliance's AdministrativeMfaSatisfied.
    It is FormalisationBoundary.formal when proven — Lean verified it. -/
def mfaConfigSatisfied (e : IamEvidence) : Prop :=
  e.mfaRequired = true ∧ e.conditionalAccessEnabled = true

/-- Risk acceptance is on file (formalisable: it is or it isn't). -/
def riskAcceptanceActive (e : IamEvidence) : Prop :=
  e.riskAcceptanceOnFile = true

/-- Training attestation exists (formalisable record presence). -/
def trainingRecordExists (e : IamEvidence) : Prop :=
  e.trainingAttestationExists = true

-- ============================================================
-- PART 3: Open texture — vague terms in ISO 27001 / SOC 2
-- These are the terms that Boolean predicates silently erase.
-- ============================================================

/-- "Appropriate MFA mechanism" (ISO 27001 A.8.5).
    The control requires MFA but does not mandate a specific mechanism.
    Whether TOTP, SMS OTP, FIDO2, or hardware keys are "appropriate" for a
    given threat model is a vague standard — clear core, contested penumbra.

    Authority mapping: Authority.accc stands in for the external ISO 27001
    certification body in this encoding. -/
axiom MfaMechanismIsAppropriate : IamEvidence → Prop

variable (e : IamEvidence) in
instance vague_mfa_mechanism : Vague (MfaMechanismIsAppropriate e) where
  reason := "ISO 27001 A.8.5: 'appropriate' MFA is not defined — mechanism " ++
            "suitability depends on threat model, data classification, and user " ++
            "population; no bright-line rule exists"
  authority := Authority.accc
  core := "FIDO2 hardware keys for privileged cloud accounts with access to " ++
          "production data; phishing-resistant mechanisms for admin roles"
  penumbra := "SMS OTP (SIM-swap risk), TOTP (phishing susceptibility), " ++
              "push notification fatigue attacks; whether any MFA is better " ++
              "than none for low-privilege accounts is contested"

/-- "Adequate training" (ISO 27001 A.6.3 / SOC 2 CC1.4).
    Training attestation is formalisable (record exists or does not).
    Whether training content is ADEQUATE for the risk profile is vague.

    This is the prototypical mixed control: Lean verifies record presence
    (trainingRecordExists), but adequacy requires human determination. -/
axiom TrainingIsAdequate : IamEvidence → Prop

variable (e : IamEvidence) in
instance vague_training : Vague (TrainingIsAdequate e) where
  reason := "SOC 2 CC1.4 / ISO 27001 A.6.3: 'adequate' security training has " ++
            "no statutory minimum curriculum; frequency, format, and content " ++
            "thresholds are organisation-relative and auditor-judged"
  authority := Authority.accc
  core := "Annual phishing simulation + hands-on MFA enrolment walkthrough " ++
          "documented for all staff within the past 12 months"
  penumbra := "Is a 10-minute annual e-learning module adequate? Do contractors " ++
              "require the same training as employees? Is refresher training " ++
              "triggered by role change or incident, or only by calendar?"

-- ============================================================
-- PART 4: LegalRule encoding of the MFA control
-- R1: primary obligation (ISO 27001 A.8.5)
-- R2: risk acceptance defeats the gap (higher-priority exception)
-- R3: compensating control — partial satisfaction
-- ============================================================

/-- R1: Primary MFA obligation under ISO 27001 A.8.5.
    OBLIGATORY: MFA must be configured and enforced for privileged accounts.
    This is the direct LegalLean replacement for the Boolean predicate.

    conclusion: wraps mfaConfigSatisfied — the formalisable fragment — in a
    FormalisationBoundary.formal when the rule fires. The vague residual
    (appropriate mechanism) is handled separately in R1's defeatedBy annotation
    and in the boundary-tagged functions below. -/
def R1_MfaObligation : LegalRule IamEvidence where
  id := "R1-MFA-ISO27001-A8.5"
  description := "ISO 27001 A.8.5: multi-factor authentication shall be used " ++
                 "for privileged accounts. MFA must be required and conditional " ++
                 "access policies must enforce it."
  modality := Deontic.obligatory
  priority := ⟨1, "ISO 27001:2022 Annex A control A.8.5"⟩
  conclusion := fun e => mfaConfigSatisfied e
  defeatedBy := ["R2-RiskAcceptance", "R3-CompensatingControl"]

/-- R2: Board/CISO risk acceptance defeats the MFA gap.
    PERMITTED: an organisation may formally accept residual risk when
    implementing MFA is not feasible in the assessment period.

    Risk acceptance is lex specialis [more specific rule overrides the general]:
    it acknowledges the gap (R1's conclusion cannot be established) and
    replaces the obligation with a documented exception. This is the
    non-monotonic step — adding a risk acceptance REMOVES the adverse
    finding that would follow from R1 failing. -/
def R2_RiskAcceptance : LegalRule IamEvidence where
  id := "R2-RiskAcceptance"
  description := "A time-boxed, CISO/Board-approved risk acceptance is on file " ++
                 "documenting the MFA gap, residual risk level, and remediation " ++
                 "timeline. Defeats the primary MFA obligation for the acceptance period."
  modality := Deontic.permitted
  priority := ⟨2, "ISO 27001:2022 clause 6.1.3 (risk treatment) — lex specialis"⟩
  conclusion := fun e => riskAcceptanceActive e
  defeatedBy := []
  applicable := fun e => e.riskAcceptanceOnFile

/-- R3: Compensating control — partial satisfaction (lex specialis exception).
    PERMITTED: a compensating control (e.g. privileged access workstation,
    network segmentation, enhanced logging) may partially substitute for MFA
    where full MFA deployment is temporarily infeasible.

    This is defeasible itself: R2 (risk acceptance) takes priority over R3
    if both apply, because risk acceptance is a higher-specificity exception. -/
def R3_CompensatingControl : LegalRule IamEvidence where
  id := "R3-CompensatingControl"
  description := "A documented compensating control (privileged access workstation, " ++
                 "network segmentation, enhanced SIEM alerting) reduces residual " ++
                 "risk where MFA cannot be fully deployed. Partially defeats the " ++
                 "primary obligation gap for the covered accounts."
  modality := Deontic.permitted
  priority := ⟨2, "ISO 27001:2022 clause 6.1.3 — compensating control, lex specialis"⟩
  conclusion := fun e => ¬(mfaConfigSatisfied e)
  defeatedBy := ["R2-RiskAcceptance"]

-- ============================================================
-- PART 5: Defeat relations
-- ============================================================

/-- D1: Risk acceptance defeats the primary MFA obligation.
    When a formal risk acceptance is in place, the obligation gap does not
    constitute a finding — the organisation has elected risk acceptance as
    its treatment under ISO 27001 clause 6.1.3.

    Strict = false: the risk acceptance can itself be challenged (e.g. if
    the acceptance period has expired, or the acceptance was not Board-level). -/
def D1_RiskAcceptanceDefeatsMfa : Defeats where
  defeater := "R2-RiskAcceptance"
  defeated := "R1-MFA-ISO27001-A8.5"
  reason := "ISO 27001:2022 clause 6.1.3 risk treatment option: organisation " ++
            "has explicitly accepted the residual risk of MFA gap with documented " ++
            "rationale and remediation timeline approved at appropriate authority level"
  strict := false

/-- D2: Risk acceptance also defeats the compensating control route.
    If a formal risk acceptance exists, a compensating control is unnecessary —
    the acceptance supersedes the partial-satisfaction route.

    Strict = false: same caveat as D1. -/
def D2_RiskAcceptanceDefeasCompensating : Defeats where
  defeater := "R2-RiskAcceptance"
  defeated := "R3-CompensatingControl"
  reason := "Risk acceptance (R2) is a higher-specificity exception than a " ++
            "compensating control (R3): once risk is formally accepted, the " ++
            "partial-satisfaction route is moot"
  strict := false

/-- All defeat relations for this control. -/
def allDefeats : List Defeats :=
  [D1_RiskAcceptanceDefeatsMfa, D2_RiskAcceptanceDefeasCompensating]

-- ============================================================
-- PART 6: Control evaluation — the migration's payoff
-- Returns FormalisationBoundary, not Bool
-- ============================================================

/-- Evaluate the MFA control for a given evidence record.
    Returns FormalisationBoundary Prop — the type that distinguishes
    formalisable from human-determinable findings.

    Migration payoff: the original Boolean predicate either passes (true)
    or fails (false). This function returns:
    - formal: both Boolean conditions met AND no risk acceptance needed
    - boundary: formalisable conditions met but mechanism appropriateness
      requires human determination (auditor / certification body)
    - mixed: risk acceptance on file — formalisable part (record exists)
      is verified; adequacy of the acceptance requires human review -/
def evaluateMfaControl (e : IamEvidence) : FormalisationBoundary Prop :=
  if e.mfaRequired && e.conditionalAccessEnabled then
    -- Boolean conditions satisfied (FormalisationBoundary.formal fragment).
    -- However, mechanism appropriateness is vague — return mixed.
    FormalisationBoundary.mixed
      ("MFA configuration flags satisfied: mfaRequired = true, " ++
       "conditionalAccessEnabled = true. Mechanism deployed: " ++ e.mfaMechanism)
      ("Mechanism appropriateness (ISO 27001 A.8.5 'appropriate') requires " ++
       "auditor determination: is '" ++ e.mfaMechanism ++
       "' commensurate with the organisation's threat model and data classification?")
  else if e.riskAcceptanceOnFile then
    -- Control gap + risk acceptance on file: the gap is known but accepted.
    -- Adequacy of the acceptance itself (correct authority level, expiry date) is vague.
    FormalisationBoundary.boundary
      ("MFA configuration gap identified. Risk acceptance on file: " ++
       "riskAcceptanceOnFile = true. Auditor must verify: (1) acceptance was " ++
       "approved at appropriate authority level (CISO/Board), (2) acceptance " ++
       "period has not expired, (3) remediation timeline is in place.")
      Authority.accc
  else
    -- Gap with no risk acceptance and no compensating control: adverse finding.
    -- The finding itself is formal (Boolean conditions not met); the severity
    -- classification ("critical" vs "high") requires human determination.
    FormalisationBoundary.boundary
      ("MFA control gap: mfaRequired = " ++ toString e.mfaRequired ++
       ", conditionalAccessEnabled = " ++ toString e.conditionalAccessEnabled ++
       ". No risk acceptance on file. Adverse finding under ISO 27001 A.8.5. " ++
       "Severity classification and remediation priority require auditor determination.")
      Authority.accc

/-- Training attestation evaluation.
    This is the prototypical boundary control: record presence is formal,
    adequacy is always at the boundary.

    Corresponds to RequiresHumanDetermination (TrainingIsAdequate e):
    the type system expresses that we CANNOT produce a formal proof of
    TrainingIsAdequate — only a boundary annotation. -/
def evaluateTrainingAttestation (e : IamEvidence) : FormalisationBoundary Prop :=
  if e.trainingAttestationExists then
    -- Record exists (formalisable). But adequacy is vague.
    FormalisationBoundary.boundary
      ("Training attestation record exists (trainingAttestationExists = true). " ++
       "Whether the training content and frequency constitute 'adequate' awareness " ++
       "under SOC 2 CC1.4 / ISO 27001 A.6.3 requires auditor determination. " ++
       "Factors: curriculum coverage, recency (within 12 months?), evidence of " ++
       "comprehension (quiz scores, attestation signatures).")
      Authority.accc
  else
    -- No record: adverse finding (formalisable). Severity still vague.
    FormalisationBoundary.boundary
      ("No training attestation on file. Adverse finding under SOC 2 CC1.4 / " ++
       "ISO 27001 A.6.3. Auditor must determine severity and whether this " ++
       "constitutes a material weakness vs a minor non-conformity.")
      Authority.accc

-- ============================================================
-- PART 7: Theorems — properties of the compliance control
-- ============================================================

/-- Theorem CC1: A gap without risk acceptance always yields a boundary finding.
    This formalises the auditor's default: absent a formal risk acceptance,
    the solver cannot produce a formal conclusion — it must defer to the
    certification body.

    Legal / compliance significance: this is the type-level encoding of the
    ISO 27001 principle that an unmitigated control gap is never self-resolving.
    The certification body (Authority.accc in our proxy mapping) must adjudicate
    the severity and remediation path. -/
theorem gap_without_acceptance_yields_boundary
    (e : IamEvidence)
    (h_gap : ¬(mfaConfigSatisfied e))
    (h_no_acceptance : e.riskAcceptanceOnFile = false) :
    ∃ reason auth, evaluateMfaControl e = FormalisationBoundary.boundary reason auth := by
  simp only [mfaConfigSatisfied] at h_gap
  -- Derive that the Bool &&-expression is false by case-splitting on both Bool fields.
  have h_and_false : (e.mfaRequired && e.conditionalAccessEnabled) = false := by
    cases h1 : e.mfaRequired <;> cases h2 : e.conditionalAccessEnabled <;>
      simp_all
  simp only [evaluateMfaControl, h_and_false, h_no_acceptance]
  exact ⟨_, _, rfl⟩

/-- Theorem CC2: Training attestation evaluation is always at the boundary.
    Whether the attestation exists or not, the result is always
    FormalisationBoundary.boundary — never formal.

    This is the key theorem for compliance documentation: no machine-only
    check can certify "adequate training". The auditor always has the
    final word. This directly expresses the RequiresHumanDetermination
    typeclass instance on TrainingIsAdequate: Lean cannot produce a proof
    of TrainingIsAdequate, only a boundary annotation. -/
theorem training_evaluation_always_boundary (e : IamEvidence) :
    ∃ reason auth,
      evaluateTrainingAttestation e = FormalisationBoundary.boundary reason auth := by
  simp only [evaluateTrainingAttestation]
  cases h : e.trainingAttestationExists <;> simp <;> exact ⟨_, _, rfl⟩

/-- Theorem CC3: R1 and R2 have distinct deontic modalities.
    R1 is obligatory (the organisation MUST implement MFA);
    R2 is permitted (the organisation MAY formally accept the risk).

    Compliance significance: risk acceptance is not a blanket exemption —
    it is a discretionary permission that requires deliberate exercise.
    The deontic distinction (obligatory vs permitted) is legally meaningful
    and is preserved in the type system. -/
theorem R1_R2_deontic_distinct :
    R1_MfaObligation.modality ≠ R2_RiskAcceptance.modality := by
  simp [R1_MfaObligation, R2_RiskAcceptance]

/-- Theorem CC4: The defeat graph is acyclic (no self-defeat).
    No rule in allDefeats has defeater = defeated.

    Correctness invariant [property that must always hold]: a self-defeating
    rule would make the rule corpus inconsistent — the rule would simultaneously
    establish and retract its own conclusion. This theorem proves our
    encoding satisfies the acyclicity condition. -/
theorem defeat_acyclicity :
    ∀ d ∈ allDefeats, d.defeater ≠ d.defeated := by
  intro d hd
  simp [allDefeats] at hd
  rcases hd with rfl | rfl
  · simp [D1_RiskAcceptanceDefeatsMfa]
  · simp [D2_RiskAcceptanceDefeasCompensating]

/-- Theorem CC5: When MFA is fully configured AND no risk acceptance is needed,
    the formalisable core (mfaConfigSatisfied) holds.

    This is the positive direction: given Boolean evidence, we can construct
    a proof of the formalisable fragment. Lean verifies this at compile time —
    it is the exact analogue of OpenCompliance's AdministrativeMfaSatisfied,
    now embedded in the LegalLean type system.

    The mixed boundary for mechanism appropriateness is a SEPARATE concern:
    mfaConfigSatisfied is formalisable; MfaMechanismIsAppropriate is vague.
    LegalLean keeps them distinct rather than conflating them in one Bool. -/
theorem mfa_config_holds_when_flags_set
    (e : IamEvidence)
    (h_mfa : e.mfaRequired = true)
    (h_ca : e.conditionalAccessEnabled = true) :
    mfaConfigSatisfied e := by
  simp [mfaConfigSatisfied, h_mfa, h_ca]

/-- Theorem CC6: R2 is listed in R1's defeatedBy set.
    Structural proof that the defeat relation is correctly encoded:
    R1 explicitly declares R2 as a potential defeater, so the solver
    will correctly apply defeat resolution when risk acceptance is active. -/
theorem risk_acceptance_is_declared_defeater :
    "R2-RiskAcceptance" ∈ R1_MfaObligation.defeatedBy := by
  simp [R1_MfaObligation]

/-- Theorem CC7: Both defeat relations are non-strict.
    All defeats in allDefeats have strict = false, meaning they are themselves
    defeasible [can be overridden by higher-priority evidence].

    Compliance significance: a risk acceptance can be challenged (expired,
    wrong authority level, inadequate documentation). Non-strict defeat
    preserves the ability to re-open a risk acceptance finding during the
    certification audit. -/
theorem all_defeats_are_non_strict :
    ∀ d ∈ allDefeats, d.strict = false := by
  intro d hd
  simp [allDefeats] at hd
  rcases hd with rfl | rfl
  · simp [D1_RiskAcceptanceDefeatsMfa]
  · simp [D2_RiskAcceptanceDefeasCompensating]

end LegalLean.CaseStudies.ComplianceControl
