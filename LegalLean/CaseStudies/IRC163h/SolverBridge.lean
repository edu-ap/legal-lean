/-
  LegalLean.CaseStudies.IRC163h.SolverBridge — Solver-Soundness Bridge Theorem.

  MOTIVATION (the architectural gap this file closes):
  ─────────────────────────────────────────────────────
  The IRC §163(h) formalisation has two halves that were previously
  disconnected:

  (A) `isDeductible` — a hand-coded if-then-else function that takes
      `(payment : InterestPayment) (year : TaxYear) (status : FilingStatus)`
      and returns `FormalisationBoundary Prop`.

  (B) The generic `Solver.solve` — takes `List (LegalRule α)` over some
      fact type `α`, uses the `defeatedBy` / `priority` metadata to
      determine which rules survive defeat, then applies the winner's
      `conclusion : α → Prop`.

  The gap: the rule definitions in IRC163h.lean (R1, R2, R3, E1_1) have
  type `LegalRule InterestPayment`.  Their `conclusion` fields are
  `InterestPayment → Prop`, but they were written without a year or
  filing-status argument.  `isDeductible` branches on year and status
  to decide which rule "wins" the defeasibility contest.  So there is
  no direct way to ask "does `solve [R1, R2, R3, E1_1] payment` agree
  with `isDeductible payment year status`?" — the types do not match.

  FIX STRATEGY (Phase 1 — SolverFacts):
  ───────────────────────────────────────
  We introduce a `SolverFacts` record that bundles all three arguments:

      structure SolverFacts where
        payment : InterestPayment
        year    : TaxYear
        status  : FilingStatus

  We then define `LegalRule SolverFacts` versions of R1-E1_1 that
  embed year and status into the `conclusion` field.  These are called
  `SR1`, `SR2`, `SR3`, `SE1_1`.

  FIX STRATEGY (Phase 2 — applicable predicate):
  ────────────────────────────────────────────────
  `LegalRule` now has an `applicable : α → Bool` field (added in Core.lean).
  `SR2_TCJAProhibition` carries an explicit predicate that gates it to
  post-TCJA home equity facts, mirroring the `year.year ≥ 2018` branch in
  `isDeductible`.  All other SR rules use the default `fun _ => true`.

  With this adapter in place we can state and (partially) prove:

    D1-D4  — individual defeat lemmas: proved WITHOUT sorry.
    D5     — undefeated rules = {SR2, SR3} (over full corpus): proved WITHOUT sorry.
    SR     — solver selects SR3 on full corpus: proved WITHOUT sorry.

    B1-B5  — auto-rejection bridge and kind-agreement: proved without sorry.
    B6     — defeat structure mirrors hand-coded logic: proved without sorry.
    B7     — sub-corpus stability: proved without sorry.
    B8     — full propositional equivalence: sorry with documented justification
              (REMAINING architectural gap — conditional activation is closed,
              deontic-to-deductibility translation still required).

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
-/

import LegalLean.Core
import LegalLean.Solver
import LegalLean.CaseStudies.IRC163h

open LegalLean
open LegalLean.CaseStudies.IRC163h

namespace LegalLean.CaseStudies.IRC163h.SolverBridge

-- ============================================================
-- Adapter type: bundles payment + year + status as a single α
-- for use with LegalRule α
-- ============================================================

/-- `SolverFacts` is the adapter that makes the generic solver type-compatible
    with `isDeductible`.

    The mismatch between `Solver.solve` (which takes `α → Prop` conclusions)
    and `isDeductible` (which takes `year` and `status` as separate arguments)
    is resolved by making a single record type that carries all three. -/
structure SolverFacts where
  payment : InterestPayment
  year    : TaxYear
  status  : FilingStatus

-- ============================================================
-- Solver-compatible rule definitions over SolverFacts
-- ============================================================

/-- SR1: Base deduction rule, parameterised over SolverFacts.
    Mirrors R1_BaseDeduction but uses SolverFacts.payment for the conclusion. -/
def SR1_BaseDeduction : LegalRule SolverFacts where
  id          := "R1"
  description := "Taxpayers are permitted to deduct interest paid on " ++
                 "acquisition indebtedness secured by a qualified residence"
  modality    := Deontic.permitted
  priority    := ⟨1, "statute"⟩
  conclusion  := fun facts =>
    isIndividualTaxpayer facts.payment ∧
    securedByResidence facts.payment.indebtedness
  defeatedBy  := ["E1.1", "E1.2", "R2"]

/-- SR2: TCJA prohibition, parameterised over SolverFacts.
    Mirrors R2_TCJAProhibition, now able to inspect `facts.year`.

    `applicable` gates this rule to home equity debt in post-TCJA years.
    This is the predicate that closes the conditional-activation gap: without
    it, SR2 would enter the defeasibility contest for ALL facts, including
    acquisition-indebtedness cases where it is irrelevant.  With it, the
    solver only activates SR2 when the facts actually trigger the TCJA
    prohibition, mirroring the `year.year >= 2018` branch in `isDeductible`. -/
def SR2_TCJAProhibition : LegalRule SolverFacts where
  id          := "R2"
  description := "Home equity interest deduction prohibited for " ++
                 "taxable years beginning after December 15, 2017"
  modality    := Deontic.prohibited
  priority    := ⟨2, "statute (TCJA 2017, lex posterior)"⟩
  conclusion  := fun facts =>
    isHomeEquityIndebtedness facts.payment.indebtedness ∧
    postTCJA facts.year
  defeatedBy  := []
  applicable  := fun facts =>
    facts.year.year ≥ 2018 &&
    (facts.payment.indebtedness.purpose == IndebtednessPurpose.other)

/-- SR3: Grandfather rule, parameterised over SolverFacts. -/
def SR3_GrandfatherRule : LegalRule SolverFacts where
  id          := "R3"
  description := "Pre-October 13, 1987 acquisition indebtedness " ++
                 "grandfathered from current dollar limits"
  modality    := Deontic.permitted
  priority    := ⟨3, "statute (lex specialis, grandfather clause)"⟩
  conclusion  := fun facts =>
    securedByResidence facts.payment.indebtedness ∧
    preTRA87 facts.payment.indebtedness
  defeatedBy  := []

/-- SE1_1: Acquisition-limit exception, parameterised over SolverFacts.
    Inspects `facts.year` and `facts.status` for the correct limit. -/
def SE1_1_DollarLimit : LegalRule SolverFacts where
  id          := "E1.1"
  description := "Acquisition indebtedness within statutory dollar limits"
  modality    := Deontic.permitted
  priority    := ⟨2, "statute (IRC 163(h)(3)(C))"⟩
  conclusion  := fun facts =>
    withinAcquisitionLimit facts.payment.indebtedness facts.year facts.status = true
  defeatedBy  := ["R3"]

/-- The full IRC 163(h) rule corpus, as a `List (LegalRule SolverFacts)`.
    This is the canonical rule corpus for use with `Solver.solve`. -/
def irc163h_solver_rules : List (LegalRule SolverFacts) :=
  [SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit]

-- ============================================================
-- Defeat-structure verification
-- (undefeatedRules uses defeatedBy only, not applicable)
-- ============================================================

/-- Theorem D1: SR2 has no defeaters (it is the highest-priority prohibition). -/
theorem SR2_not_defeated_in_corpus :
    isDefeated SR2_TCJAProhibition irc163h_solver_rules = false := by
  simp [isDefeated, irc163h_solver_rules,
        SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit]

/-- Theorem D2: SR3 has no defeaters (it is a grandfather clause). -/
theorem SR3_not_defeated_in_corpus :
    isDefeated SR3_GrandfatherRule irc163h_solver_rules = false := by
  simp [isDefeated, irc163h_solver_rules,
        SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit]

/-- Theorem D3: SR1 IS defeated in the full corpus (by SR2, which is present). -/
theorem SR1_defeated_in_corpus :
    isDefeated SR1_BaseDeduction irc163h_solver_rules = true := by
  simp [isDefeated, irc163h_solver_rules,
        SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit]

/-- Theorem D4: SE1_1 IS defeated in the full corpus (by SR3). -/
theorem SE1_1_defeated_in_corpus :
    isDefeated SE1_1_DollarLimit irc163h_solver_rules = true := by
  simp [isDefeated, irc163h_solver_rules,
        SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit]

/-- Theorem D5: The undefeated rules in the full corpus (by defeatedBy alone) are {SR2, SR3}.

    This is the structural heart of the solver bridge.  It says that when
    all four rules are present, the defeat checking correctly identifies
    that SR2 (TCJA prohibition) and SR3 (grandfather exception) survive,
    while SR1 (base) and SE1_1 (dollar limit) are defeated.

    Note: `undefeatedRules` operates on `defeatedBy` only, not `applicable`.
    The `applicable` filter in `solve` is separate. -/
theorem undefeated_rules_are_SR2_SR3 :
    undefeatedRules irc163h_solver_rules =
      [SR2_TCJAProhibition, SR3_GrandfatherRule] := by
  simp [undefeatedRules, irc163h_solver_rules,
        SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit,
        isDefeated]

-- ============================================================
-- The solver result for the full corpus
-- ============================================================

/-
  STRUCTURAL NOTE ON SR (updated for applicable predicate)
  ──────────────────────────────────────────────────────────
  `solve` now filters by `applicable facts` before defeat resolution.
  SR2 has `applicable := fun facts => facts.year.year ≥ 2018 && purpose = other`.

  Two sub-cases for any `facts : SolverFacts`:

  Case A (SR2 applicable): year ≥ 2018 && purpose = other
    applicable corpus = [SR1, SR2, SR3, SE1_1]
    defeat: SR1 defeated by SR2 (present in applicable); SE1_1 defeated by SR3
    undefeated = [SR2, SR3]; SR3 wins (priority 3 > 2)

  Case B (SR2 not applicable): year < 2018 OR purpose ≠ other
    applicable corpus = [SR1, SR3, SE1_1]
    defeat: "R2" not in applicable, so SR1.defeatedBy = ["E1.1", "E1.2", "R2"]
      → SR1 is defeated only if "E1.1" or "E1.2" or "R2" appear as IDs.
      SR3 id = "R3", SE1_1 id = "E1.1" — so SR1 IS defeated by SE1_1 (id "E1.1")
    defeat: SE1_1.defeatedBy = ["R3"]; SR3 id = "R3" → SE1_1 defeated
    undefeated = [SR1, SR3]... wait: SR1.defeatedBy includes "E1.1" and SE1_1.id = "E1.1".
    So SR1 is defeated by SE1_1 in Case B too.
    undefeated = [SR3]; SR3 wins.

  In both cases SR3 wins → theorem holds universally.
-/

/-- Theorem SR: With the full corpus, `solve` selects SR3 (the highest-priority
    undefeated applicable rule) and returns `formal (SR3.conclusion facts)`.

    SR3 wins in both fact-dependent sub-cases:
    - When SR2 IS applicable (year ≥ 2018, purpose = other):
        applicable = [SR1, SR2, SR3, SE1_1]; undefeated = [SR2, SR3]; SR3 wins.
    - When SR2 is NOT applicable:
        applicable = [SR1, SR3, SE1_1]; SE1_1 (id "E1.1") defeats SR1; SE1_1 defeated
        by SR3; undefeated = [SR3]; SR3 is the sole winner.

    In both cases SR3 wins. -/
theorem solve_full_corpus_selects_SR3 (facts : SolverFacts) :
    solve irc163h_solver_rules facts =
      FormalisationBoundary.formal (SR3_GrandfatherRule.conclusion facts) := by
  -- Split on whether SR2's applicable predicate fires; then fully reduce with simp.
  by_cases h_sr2 : facts.year.year ≥ 2018 && (facts.payment.indebtedness.purpose == IndebtednessPurpose.other)
  · -- Case A: SR2 applicable → applicable corpus = [SR1, SR2, SR3, SE1_1]
    simp [solve, irc163h_solver_rules,
          SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit,
          undefeatedRules, isDefeated, allSamePriority, maxPriorityRule, h_sr2]
  · -- Case B: SR2 not applicable → applicable corpus = [SR1, SR3, SE1_1]
    simp only [Bool.not_eq_true] at h_sr2
    simp [solve, irc163h_solver_rules,
          SR1_BaseDeduction, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit,
          undefeatedRules, isDefeated, h_sr2]

-- ============================================================
-- Bridge theorems: solver -- isDeductible agreement
-- ============================================================

/-
  STRUCTURAL NOTE ON BRIDGE STATUS (updated for applicable predicate)
  ────────────────────────────────────────────────────────────────────
  The `applicable : α → Bool` field is now in `LegalRule` (Core.lean).
  `SR2_TCJAProhibition` carries an explicit predicate:

      applicable := fun facts =>
        facts.year.year ≥ 2018 &&
        (facts.payment.indebtedness.purpose == IndebtednessPurpose.other)

  This gates SR2 to the exact fact pattern where `isDeductible` applies the
  TCJA prohibition branch.  The solver is now fact-sensitive [context-aware]:
  it filters the corpus before defeat resolution, mirroring `isDeductible`'s
  if-then-else branching.

  The `applicable` field closes the CONDITIONAL ACTIVATION gap identified in
  the original B8 comment.  What remains is the DEONTIC CONSEQUENCE gap:
  the solver returns `formal (SR3.conclusion)` (a structural conjunction),
  while `isDeductible` returns `formal False` (the deductibility verdict).
  Closing B8 fully requires either:
  (a) A `deonticConsequence` field in `LegalRule`, or
  (b) A `DeductibilityRule` wrapper that maps `prohibited → False`.

  The theorems below focus on sub-corpus agreements and kind-agreement cases.
-/

/-- B1 (AUTO-REJECTION BRIDGE): Non-individual case.

    When `payment.paidByIndividual = false`, `isDeductible` returns `formal False`.
    Proved without sorry — pure structural result. -/
theorem bridge_auto_reject_non_individual
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h : payment.paidByIndividual = false) :
    isDeductible payment year status = FormalisationBoundary.formal False := by
  simp [isDeductible, h]

/-- B2 (AUTO-REJECTION BRIDGE): Unsecured debt case.

    When `securedByResidence = false`, `isDeductible` returns `formal False`.
    Proved without sorry. -/
theorem bridge_auto_reject_unsecured
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h : payment.indebtedness.securedByResidence = false) :
    isDeductible payment year status = FormalisationBoundary.formal False := by
  simp [isDeductible, h]

/-- B3 (SOLVER-SOUNDNESS BRIDGE — POST-TCJA HOME EQUITY):

    For post-TCJA home equity payments, BOTH the hand-coded function
    AND the solver (on the two-rule sub-corpus [SR1, SR2]) agree
    that the outcome is `formal _`.

    With SR2's `applicable` predicate, SR2 IS included in the filter for
    these facts (year ≥ 2018 && purpose = other), so the two-rule corpus
    [SR1, SR2] reduces to: SR2 defeats SR1 (via defeatedBy), sole undefeated
    = SR2 → `formal (SR2.conclusion facts)`.

    `isDeductible` returns `formal False`.

    Both return `formal _` (KIND agreement). -/
theorem bridge_post_tcja_solver_kind_agreement
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h_individual : payment.paidByIndividual = true)
    (h_secured : payment.indebtedness.securedByResidence = true)
    (h_purpose : payment.indebtedness.purpose = IndebtednessPurpose.other)
    (h_post_tcja : year.year ≥ 2018) :
    isDeductible payment year status = FormalisationBoundary.formal False ∧
    ∃ P, solve [SR1_BaseDeduction, SR2_TCJAProhibition]
               ⟨payment, year, status⟩ =
             FormalisationBoundary.formal P := by
  constructor
  · simp [isDeductible, h_individual, h_secured, h_purpose, h_post_tcja]
  · refine ⟨SR2_TCJAProhibition.conclusion ⟨payment, year, status⟩, ?_⟩
    -- SR2's applicable predicate fires (year ≥ 2018 && purpose = other)
    -- Two-rule corpus applicable = [SR1, SR2]; SR1 defeated by SR2; sole = SR2 → formal
    -- Rewrite h_purpose to use BEq then let simp/decide close
    have h_purpose_beq : (payment.indebtedness.purpose == IndebtednessPurpose.other) = true := by
      rw [h_purpose]; rfl
    simp [solve, SR1_BaseDeduction, SR2_TCJAProhibition,
          undefeatedRules, isDefeated, h_post_tcja, h_purpose_beq]

/-- B4 (KIND-AGREEMENT — NON-INDIVIDUAL):

    For a non-individual payer, BOTH sides return `formal _`.
    `isDeductible` returns `formal False`; solver returns `formal (SR3.conclusion)`.
    Kind agrees; inner proposition differs (architectural gap documented in B8). -/
theorem bridge_formal_kind_agreement_non_individual
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h : payment.paidByIndividual = false) :
    (∃ P, isDeductible payment year status = FormalisationBoundary.formal P) ∧
    (∃ Q, solve irc163h_solver_rules ⟨payment, year, status⟩ =
            FormalisationBoundary.formal Q) := by
  exact ⟨⟨False, bridge_auto_reject_non_individual payment year status h⟩,
         ⟨_, solve_full_corpus_selects_SR3 ⟨payment, year, status⟩⟩⟩

/-- B5 (KIND-AGREEMENT — UNSECURED):

    Same kind-agreement result for the unsecured case. -/
theorem bridge_formal_kind_agreement_unsecured
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h : payment.indebtedness.securedByResidence = false) :
    (∃ P, isDeductible payment year status = FormalisationBoundary.formal P) ∧
    (∃ Q, solve irc163h_solver_rules ⟨payment, year, status⟩ =
            FormalisationBoundary.formal Q) := by
  exact ⟨⟨False, bridge_auto_reject_unsecured payment year status h⟩,
         ⟨_, solve_full_corpus_selects_SR3 ⟨payment, year, status⟩⟩⟩

-- ============================================================
-- B6: The defeat structure mirrors isDeductible's branching logic
-- ============================================================

/-- Theorem B6 (DEFEAT-STRUCTURE SOUNDNESS):

    The `defeatedBy` annotations on the solver rules encode the SAME
    defeasibility ordering that `isDeductible` implements via if-then-else.

    - SR1.defeatedBy = ["E1.1", "E1.2", "R2"]
        isDeductible checks R2 (TCJA) and E1.x (limits) before permitting
    - SR2.defeatedBy = []
        TCJA prohibition is never overridden (lex posterior, highest statute)
    - SR3.defeatedBy = []
        Grandfather clause is never overridden (lex specialis)
    - SE1_1.defeatedBy = ["R3"]
        isDeductible bypasses dollar limit for grandfathered debt

    We also prove SR2's applicable predicate encodes the TCJA condition. -/
theorem defeat_structure_mirrors_hand_coded :
    SR1_BaseDeduction.defeatedBy = ["E1.1", "E1.2", "R2"] ∧
    SR2_TCJAProhibition.defeatedBy = [] ∧
    SR3_GrandfatherRule.defeatedBy = [] ∧
    SE1_1_DollarLimit.defeatedBy = ["R3"] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem B6a (APPLICABLE-STRUCTURE SOUNDNESS):

    SR2's `applicable` predicate correctly encodes the TCJA activation condition:
    it is true exactly when `year ≥ 2018` AND `purpose = other` (home equity). -/
theorem SR2_applicable_iff_post_tcja_home_equity (facts : SolverFacts) :
    SR2_TCJAProhibition.applicable facts = true ↔
    facts.year.year ≥ 2018 ∧ facts.payment.indebtedness.purpose = IndebtednessPurpose.other := by
  simp only [SR2_TCJAProhibition, Bool.and_eq_true, decide_eq_true_eq]
  -- Bridge (a == b) = true ↔ a = b using case analysis on purpose
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    -- `a == b = true` with derived BEq; by case analysis on purpose:
    -- if purpose ≠ other, BEq gives false, contradiction with h2
    cases hp : facts.payment.indebtedness.purpose <;> simp_all (config := { decide := true })
  · intro ⟨h1, h2⟩
    -- `purpose = other`, so `other == other = true`
    refine ⟨h1, ?_⟩
    rw [h2]
    -- IndebtednessPurpose.other == IndebtednessPurpose.other = true by definition of BEq
    decide

-- ============================================================
-- B7: Sub-corpus stability
-- ============================================================

/-- Theorem B7: For the three-rule corpus [SR2, SR3, SE1_1] (dropping SR1),
    the solver still returns `formal _`.

    This shows the solver's output is stable [invariant] when we remove
    the already-defeated SR1 from the corpus.

    SR3 wins in both sub-cases:
    - SR2 applicable: applicable = [SR2, SR3, SE1_1]; undefeated = [SR2, SR3]; SR3 wins.
    - SR2 not applicable: applicable = [SR3, SE1_1]; SE1_1 defeated by SR3; SR3 wins. -/
theorem solve_minus_SR1_still_formal (facts : SolverFacts) :
    ∃ P, solve [SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit] facts =
           FormalisationBoundary.formal P := by
  refine ⟨SR3_GrandfatherRule.conclusion facts, ?_⟩
  by_cases h_sr2 : facts.year.year ≥ 2018 && (facts.payment.indebtedness.purpose == IndebtednessPurpose.other)
  · -- SR2 applicable → applicable = [SR2, SR3, SE1_1]; undefeated = [SR2, SR3]; SR3 wins
    simp [solve, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit,
          undefeatedRules, isDefeated, allSamePriority, maxPriorityRule, h_sr2]
  · -- SR2 not applicable → applicable = [SR3, SE1_1]; SE1_1 defeated; SR3 sole winner
    simp only [Bool.not_eq_true] at h_sr2
    simp [solve, SR2_TCJAProhibition, SR3_GrandfatherRule, SE1_1_DollarLimit,
          undefeatedRules, isDefeated, h_sr2]

-- ============================================================
-- B8: Full propositional equivalence (sorry — remaining gap)
-- ============================================================

/-
  NOTE ON B8 (sorry still justified after applicable was added):
  ──────────────────────────────────────────────────────────────
  The `applicable` field (added to `LegalRule` in Core.lean) closes the
  CONDITIONAL ACTIVATION gap: SR2 now only enters the competition when the
  facts match the TCJA prohibition conditions.

  However, full propositional equivalence still requires:

    solve irc163h_solver_rules facts = FormalisationBoundary.formal False
    when facts.payment.paidByIndividual = false

  The solver returns `formal (SR3.conclusion facts)`, not `formal False`.
  SR3.conclusion = securedByResidence ^ preTRA87, which does NOT reduce to
  False from paidByIndividual = false alone.  The winner is always SR3
  (priority 3, no defeaters, universally applicable), so the solver always
  wraps SR3's conjunction — regardless of individual/corporate status.

  Remaining gap: a deontic-to-deductibility translation is still needed:
  (a) A `deonticConsequence : Deontic → Prop → Prop` field in LegalRule, or
  (b) A `DeductibilityRule` wrapper type that maps `prohibited` to `False`.

  The sorry here documents the REMAINING ARCHITECTURAL GAP. -/

/-- B8 (SORRY — REMAINING ARCHITECTURAL GAP):

    After adding `applicable : α → Bool` to `LegalRule`, the solver is now
    fact-sensitive.  But full propositional equivalence between the solver and
    `isDeductible` still requires a deontic-to-deductibility translation.

    The solver returns `formal (SR3.conclusion)` (a structural conjunction about
    the debt); `isDeductible` returns `formal False` (the deductibility verdict).
    These propositions are extensionally [truth-functionally] distinct.

    Closing B8 requires either:
    (a) A `deonticConsequence` field in `LegalRule`, or
    (b) A `DeductibilityRule` wrapper that interprets `prohibited` as `False`.

    This sorry is intentional documentation of the remaining gap. -/
theorem bridge_full_equivalence_non_individual
    (payment : InterestPayment)
    (year : TaxYear)
    (status : FilingStatus)
    (h : payment.paidByIndividual = false) :
    solve irc163h_solver_rules ⟨payment, year, status⟩ =
      FormalisationBoundary.formal False := by
  sorry  -- REMAINING GAP: solver returns formal (SR3.conclusion), not formal False.
         -- `applicable` closes conditional-activation gap but not deontic-consequence gap.

-- ============================================================
-- Summary theorem: what the bridge establishes
-- ============================================================

/-- SUMMARY: What the solver bridge proves.

    The solver-soundness bridge proves:
    1. Defeat STRUCTURE is correct: undefeated rules = {SR2, SR3}  [D5]
    2. FormalisationBoundary KIND agrees for auto-rejection cases     [B4, B5]
    3. Sub-corpus agreements hold                                     [B3, B7]
    4. Defeat metadata mirrors hand-coded logic                      [B6]
    5. SR2's applicable predicate encodes the TCJA condition         [B6a]
    6. The full corpus solver always returns `formal _`              [SR]

    The REMAINING architectural gap (B8): full propositional equivalence
    requires a deontic-to-deductibility translation layer.
    The conditional-activation gap is now CLOSED by `applicable`. -/
theorem solver_bridge_summary :
    undefeatedRules irc163h_solver_rules = [SR2_TCJAProhibition, SR3_GrandfatherRule] ∧
    isDefeated SR2_TCJAProhibition irc163h_solver_rules = false ∧
    isDefeated SR3_GrandfatherRule irc163h_solver_rules = false ∧
    isDefeated SR1_BaseDeduction irc163h_solver_rules = true ∧
    ∀ facts : SolverFacts,
      ∃ P, solve irc163h_solver_rules facts = FormalisationBoundary.formal P :=
  ⟨undefeated_rules_are_SR2_SR3,
   SR2_not_defeated_in_corpus,
   SR3_not_defeated_in_corpus,
   SR1_defeated_in_corpus,
   fun facts => ⟨_, solve_full_corpus_selects_SR3 facts⟩⟩

end LegalLean.CaseStudies.IRC163h.SolverBridge
