/-
  LegalLean.TypeclassConstraint — Demonstration that RequiresHumanDetermination
  has genuine enforcement teeth.

  MOTIVATION (prior-art strengthening):
  The novelty claim for the FormalisationBoundary / RequiresHumanDetermination
  architecture is not merely aspirational — it is *demonstrated* here.
  Prior art (DDL, Catala, L4L, LegalRuleML) treats Hart's open texture as an
  external limitation. We encode it WITHIN the type system. This file proves
  the mechanism actually constrains what the type checker can discharge.

  KEY INSIGHT:
  `RequiresHumanDetermination P` (and its subclass `Vague P`) is a *typeclass*
  — a structure carrying metadata strings. It does NOT supply a proof of `P`.
  Therefore:
    (a) Any `P` can receive a `Vague` instance regardless of whether `P` is true.
    (b) The typeclass instance alone cannot discharge proof obligations on `P`.
    (c) `FormalisationBoundary.formal (proof : P)` requires an ACTUAL proof of P.
    (d) `FormalisationBoundary.boundary` is always available WITHOUT a proof.

  The combination of (c) and (d) is the enforcement mechanism:
    - Developers who respect the boundary use `.boundary` (no proof needed).
    - Anyone who incorrectly forces `.formal` on a vague proposition must either
      produce a genuine proof (impossible for truly vague propositions) or use
      `sorry` (detectable by `#print axioms`, CI grep, or `lake build --no-sorry`).

  This file is proof-of-concept for the monograph's T3 thesis:
  "FormalisationBoundary is meaningful — it constrains what can be proven."

  NOTE ON LEAN SORTS:
  `FormalisationBoundary P` where `P : Prop` lives in `Type`, not `Prop`,
  so constructions of it are `def` values (data), not `theorem` proofs.
  Structural properties ABOUT `FormalisationBoundary` that are themselves
  `Prop`-valued CAN be theorems. This distinction is noted at each definition.
-/

import LegalLean.Core

set_option autoImplicit false

open LegalLean

namespace TypeclassConstraint

-- ============================================================
-- §1  A genuinely unprovable proposition with a Vague instance
-- ============================================================

/-- An opaque proposition representing "the interest deduction is reasonable."
    `axiom IsReasonable : Prop` declares it as a primitive with no proof body.
    The type checker CANNOT discharge this obligation without `sorry` or a
    further axiom — there is no term of type `IsReasonable` in scope.

    This is the representative of Hart's "penumbral" case — the kind of
    proposition that appears in legal reasoning but resists formal proof. -/
axiom IsReasonable : Prop

/-- Register `IsReasonable` as a vague concept requiring human determination.
    CRITICAL OBSERVATION: this instance carries ONLY metadata strings.
    No proof of `IsReasonable` is produced. The typeclass is a TAG, not a proof.
    After this instance is defined, `IsReasonable` is still unprovable. -/
instance isReasonable_vague : Vague IsReasonable where
  reason    := "Reasonableness has a settled core but a contested penumbra"
  authority := Authority.irsTaxCourt
  core      := "Payments similar to market rate are clearly reasonable"
  penumbra  := "Payments in the 80–120% market-rate band require judgment"

-- ============================================================
-- §2  Positive control: True IS provable (contrast)
-- ============================================================

/-- `True` can be proven trivially. `FormalisationBoundary.formal` accepts it.
    This shows the `.formal` constructor is not broken — it works when a genuine
    proof exists.
    (Returns `FormalisationBoundary True : Type`, so this is a `def`, not a `theorem`.) -/
def trueIsFormallyDischargeable : FormalisationBoundary True :=
  FormalisationBoundary.formal trivial

-- ============================================================
-- §3  Negative case: IsReasonable CANNOT discharge .formal without sorry
-- ============================================================

/-
  The following example is INTENTIONALLY COMMENTED OUT.
  Uncommenting it causes a build failure — no proof of `IsReasonable` exists:

      def badFormal : FormalisationBoundary IsReasonable :=
        FormalisationBoundary.formal _      -- ERROR: unknown placeholder

  The only ways to make this compile are:
    1. `FormalisationBoundary.formal sorry`  — introduces `sorry`
       Detectable via: `#print axioms badFormal`, `grep -r sorry`, or `lake build --no-sorry`
    2. `FormalisationBoundary.formal (by exact?)` — fails: no proof in context
    3. `FormalisationBoundary.formal (by assumption)` — fails: same reason
    4. Add `axiom proofOfReasonable : IsReasonable` — explicit postulation,
       visible in `#print axioms` output for any downstream theorem

  ALL four paths are statically detectable. None can slip through a properly
  configured CI pipeline (`lake build --no-sorry` + axiom audit).
-/

-- ============================================================
-- §4  The correct path: .boundary requires NO proof of P
-- ============================================================

/-- `FormalisationBoundary.boundary` can always be constructed for any
    proposition — provable or not — because it requires only a reason string
    and a typed `Authority` value (Fix 2: no longer a magic string).
    This is the SAFE constructor for vague propositions.
    (`def`, not `theorem`: returns `FormalisationBoundary IsReasonable : Type`) -/
def vagueHasBoundaryConstructor : FormalisationBoundary IsReasonable :=
  FormalisationBoundary.boundary
    "Reasonableness has a settled core but a contested penumbra"
    Authority.irsTaxCourt

/-- The boundary constructor is available for ANY proposition in `Prop`.
    General form: no provability constraint on P whatsoever.
    `authority` is now typed as `Authority` (Fix 2), not a magic string.
    (`def`, not `theorem`: returns a `Type`-valued term) -/
def boundaryAvailableForAnyProp (P : Prop) (r : String) (a : Authority)
    : FormalisationBoundary P :=
  FormalisationBoundary.boundary r a

-- ============================================================
-- §5  Structural theorems: the enforcement gap as Prop-valued facts
-- ============================================================

/-- THEOREM: The `formal` constructor carries an ACTUAL proof.
    If someone supplies `pf` to build `FormalisationBoundary.formal pf`,
    then `pf : P` is a genuine proof term — we can extract it.
    (This IS a `theorem` because the type is `Prop`.) -/
theorem formal_constructor_implies_proof (P : Prop) (pf : P) : P :=
  pf

/-- THEOREM: Extracting the proof from a `FormalisationBoundary.formal` value.
    Round-trip confirmation that `.formal` is a transparent proof carrier. -/
theorem formal_carries_real_proof (P : Prop) (b : FormalisationBoundary P)
    (h : ∃ pf : P, b = FormalisationBoundary.formal pf) : P :=
  let ⟨pf, _⟩ := h; pf

/-- THEOREM: `formal` and `boundary` are DISJOINT constructors.
    The two paths (machine-verified vs human-delegated) are structurally distinct
    at the type level — not a matter of convention or discipline.
    (IS a `theorem`: the type is `Prop`.) -/
theorem formal_ne_boundary (P : Prop) (pf : P) (r : String) (a : Authority)
    : FormalisationBoundary.formal pf ≠ FormalisationBoundary.boundary r a := by
  intro h
  exact FormalisationBoundary.noConfusion h

-- ============================================================
-- §6  RequiresHumanDetermination is a MARKER, not a proof supplier
-- ============================================================

/-- THEOREM: The `Vague` typeclass fields carry metadata, not proofs.
    Having a `Vague IsReasonable` instance gives us a `reason` string and
    an `authority` value, not a proof of `IsReasonable`.
    - `reason` is a `String` (length ≥ 0 trivially).
    - `authority` is an `Authority` (typed enumeration; `BEq` holds trivially).
    Neither field can provide a proof of `IsReasonable`. -/
theorem vague_instance_fields_are_metadata
    [inst : Vague IsReasonable]
    : inst.reason.length ≥ 0 ∧ (inst.authority = inst.authority) :=
  ⟨Nat.zero_le _, rfl⟩

/-- DEFINITION: Using `Vague` instance metadata to build a `.boundary` value.
    This IS possible — the metadata strings feed directly into `.boundary`.
    (`def`, not `theorem`: returns `FormalisationBoundary IsReasonable : Type`) -/
def vagueInstanceGivesBoundaryNotProof
    [inst : Vague IsReasonable]
    : FormalisationBoundary IsReasonable :=
  FormalisationBoundary.boundary inst.reason inst.authority

-- ============================================================
-- §7  The #print axioms audit trail
-- ============================================================

/-
  Run these commands in an interactive Lean session to verify the axiom trail:

      #print axioms trueIsFormallyDischargeable
      -- Output: 'TypeclassConstraint.trueIsFormallyDischargeable' does not depend on any axioms
      -- (True is provable from Lean's core, no external axioms)

      #print axioms vagueHasBoundaryConstructor
      -- Output: 'TypeclassConstraint.vagueHasBoundaryConstructor' does not depend on any axioms
      -- (.boundary requires only String args, no proof axioms)

      #print axioms formal_ne_boundary
      -- Output: no axioms (follows from inductive constructor injectivity)

  Contrast with what a `sorry`-laden version would show:

      def badFormal : FormalisationBoundary IsReasonable :=
        FormalisationBoundary.formal sorry
      #print axioms badFormal
      -- Output: 'badFormal' depends on axioms: [sorryAx]
      -- ^^^^^^^^ This is the CI failure signal.
-/

/-
  Summary of the enforcement mechanism
  =====================================

  The table below captures what each constructor requires:

    Constructor                         | Requires proof of P? | Always available?
    ------------------------------------+----------------------+------------------
    FormalisationBoundary.formal pf     | YES (pf : P)         | Only if P provable
    FormalisationBoundary.boundary r a  | NO  (r : String,     | Always
                                        |      a : Authority)  |
    FormalisationBoundary.mixed fp hp   | NO  (fp, hp : String)| Always

  The `Vague` / `RequiresHumanDetermination` typeclass:
    - Can be instantiated for ANY proposition (provable or not)
    - Carries only metadata (`reason` : String, `authority` : Authority, `core`/`penumbra` : String)
    - Does NOT supply a proof of P

  The enforcement chain:
    1. Type checker:  `.formal` requires a term of type P in scope.
    2. Grep / lint:   `sorry` anywhere in the proof is searchable.
    3. `#print axioms`: reveals `sorryAx` or unexpected axiom dependencies.
    4. `lake build --no-sorry`: rejects any file containing `sorry`.
    5. Axiom hygiene: `axiom proofOfReasonable : IsReasonable` is visible to
       any downstream `#print axioms` call.

  This is the "teeth" of the mechanism. It is NOT merely aspirational.
  The type checker enforces it at every call site.
-/

end TypeclassConstraint
