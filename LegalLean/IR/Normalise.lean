/-
  LegalLean.IR.Normalise — Idempotent normalisation pass for IR clauses.

  Normalisation puts a Clause into a canonical form before lowering.
  The pass is IDEMPOTENT: normalise (normalise c) = normalise c.

  Four normalisation operations are performed:
    N1. Canonicalise voice → Voice.active (passive → active rewrite).
    N2. Simplify negation: double negatives → positive.
    N3. Flatten exception structure: nested exceptions merged into
        a flat defeasible list (sorted by clauseId for stability).
    N4. Sort cross-references by canonical key.

  Each operation is individually idempotent; their composition is
  therefore also idempotent.

  Proof strategy for mergeSort idempotence (N3, N4):
    We use Lean 4 core theorems (Init.Data.List.Sort):
      List.sorted_mergeSort (trans) (total) :
        ∀ l, (mergeSort l le).Pairwise le
      List.mergeSort_of_sorted :
        Pairwise le l → mergeSort l le = l
    Both operate at the Bool level (le : α → α → Bool), requiring only
    explicit trans/total witnesses — no IsAntisymm instance is needed.
    This is important because ExceptionRef has no @[ext] attribute
    (two ExceptionRefs may share a clauseId with different descriptions,
    making IsAntisymm for clauseId-ordering unprovable).

  Precedence note: in Lean 4, `=` (prec 50) binds tighter than `||`
  (prec 30), so `a || b = true` parses as `a || (b = true)`. The `||`
  then coerces `b = true : Prop` to `Bool` via `decide`, producing
  `a || decide (b = true)`. All `||`-boolean statements below use
  explicit parentheses `(a || b) = true` to avoid this trap.
-/

import LegalLean.IR.Legal

namespace LegalLean.IR.Normalise

open LegalLean.IR

-- ============================================================
-- N1: Canonicalise voice → active
-- ============================================================

/-- Rewrite a Clause's voice to Active.
    Passive and Impersonal clauses express the same normative content
    as their active equivalents; canonicalising removes this variation
    so that downstream diffing and lowering operate on a uniform form. -/
def normaliseVoice (c : Clause) : Clause :=
  { c with voice := Voice.active }

theorem normaliseVoice_idempotent (c : Clause) :
    normaliseVoice (normaliseVoice c) = normaliseVoice c := by
  simp [normaliseVoice]

-- ============================================================
-- N2: Simplify negation (double-negative → positive)
-- ============================================================

/-- Rewrite double-negative negation to positive polarity.
    "No deduction shall be disallowed" = "deduction is allowed". -/
def normaliseNegation (c : Clause) : Clause :=
  { c with negation := c.negation.normalise }

/-- Negation.normalise is idempotent at the value level. -/
theorem negation_normalise_idempotent (n : Negation) :
    n.normalise.normalise = n.normalise := by
  cases n <;> simp [Negation.normalise]

theorem normaliseNegation_idempotent (c : Clause) :
    normaliseNegation (normaliseNegation c) = normaliseNegation c := by
  simp [normaliseNegation, negation_normalise_idempotent]

-- ============================================================
-- N3: Flatten exception structure
-- ============================================================

/-- Merge a nested ExceptionStructure into a flat defeasible list.
    The canonical form is ExceptionStructure.defeasible with all
    ExceptionRef values collected and sorted by clauseId.

    Sorting by clauseId is the stability invariant that makes
    flattening idempotent: sorting an already-sorted list is a no-op. -/
def flattenExceptions (es : ExceptionStructure) : ExceptionStructure :=
  let refs := es.allRefs
  let sorted := refs.mergeSort (fun a b => a.clauseId ≤ b.clauseId)
  match sorted with
  | []   => ExceptionStructure.none
  | list => ExceptionStructure.defeasible list

-- ============================================================
-- mergeSort idempotence for clauseId ordering
-- ============================================================

private theorem clauseId_le_bool_trans (a b c : ExceptionRef)
    (hab : decide (a.clauseId ≤ b.clauseId) = true)
    (hbc : decide (b.clauseId ≤ c.clauseId) = true) :
    decide (a.clauseId ≤ c.clauseId) = true := by
  simp only [decide_eq_true_iff] at *
  exact String.le_trans hab hbc

/-- Note explicit parentheses: `(a || b) = true`, NOT `a || b = true`.
    In Lean 4, `=` has higher precedence than `||`, so the latter parses
    as `a || (b = true)` and the `||` coerces `(b = true) : Prop` to
    `Bool` via `decide`, producing a double-decide in the inferred type. -/
private theorem clauseId_le_bool_total (a b : ExceptionRef) :
    (decide (a.clauseId ≤ b.clauseId) || decide (b.clauseId ≤ a.clauseId)) = true := by
  rcases String.le_total a.clauseId b.clauseId with h | h
  · rw [decide_eq_true_iff.mpr h]; rfl
  · rw [decide_eq_true_iff.mpr h]; simp

/-- An already clauseId-sorted list is unchanged by mergeSort.
    Uses List.sorted_mergeSort + List.mergeSort_of_sorted (Lean 4 core). -/
private theorem mergeSort_clauseId_idem (refs : List ExceptionRef) :
    (refs.mergeSort (fun a b => a.clauseId ≤ b.clauseId)).mergeSort
      (fun a b => a.clauseId ≤ b.clauseId) =
    refs.mergeSort (fun a b => a.clauseId ≤ b.clauseId) :=
  List.mergeSort_of_sorted
    (List.sorted_mergeSort clauseId_le_bool_trans clauseId_le_bool_total refs)

-- ============================================================
-- N3 idempotence
-- ============================================================

/-- Flattened form has no nested constructors; flattening again is a
    no-op because allRefs on a defeasible list returns the same list
    and sorting a sorted list is stable (List.mergeSort_of_sorted). -/
theorem flattenExceptions_idempotent (es : ExceptionStructure) :
    flattenExceptions (flattenExceptions es) = flattenExceptions es := by
  simp only [flattenExceptions]
  rcases h : es.allRefs.mergeSort (fun a b => a.clauseId ≤ b.clauseId) with _ | ⟨x, xs⟩
  · -- sorted = [] → flattenExceptions produces .none → allRefs .none = [] → .none = .none
    simp [ExceptionStructure.allRefs]
  · -- sorted = x::xs → flattenExceptions produces .defeasible (x::xs)
    -- allRefs (.defeasible (x::xs)) = x::xs
    -- (x::xs).mergeSort = x::xs by mergeSort_clauseId_idem
    have h_idem : (x :: xs).mergeSort (fun a b => a.clauseId ≤ b.clauseId) = x :: xs := by
      rw [← h]; exact mergeSort_clauseId_idem es.allRefs
    simp [ExceptionStructure.allRefs, h_idem]

def normaliseExceptions (c : Clause) : Clause :=
  { c with exceptionStructure := flattenExceptions c.exceptionStructure }

theorem normaliseExceptions_idempotent (c : Clause) :
    normaliseExceptions (normaliseExceptions c) = normaliseExceptions c := by
  simp [normaliseExceptions, flattenExceptions_idempotent]

-- ============================================================
-- N4: Sort cross-references (canonical ordering)
-- ============================================================

/-- Assign a numeric key to CrossRefScope for sorting.
    The prefix character ensures the three constructors form
    a total, prefix-free order: "0" < "1…" < "2…". -/
def crossRefKey : CrossRefScope → String
  | .none                   => "0"
  | .intraStatute t         => "1" ++ t
  | .interStatute s t       => "2" ++ s ++ t

-- ============================================================
-- mergeSort idempotence for crossRefKey ordering
-- ============================================================

private theorem crossRefKey_le_bool_trans (a b c : CrossRefScope)
    (hab : decide (crossRefKey a ≤ crossRefKey b) = true)
    (hbc : decide (crossRefKey b ≤ crossRefKey c) = true) :
    decide (crossRefKey a ≤ crossRefKey c) = true := by
  simp only [decide_eq_true_iff] at *
  exact String.le_trans hab hbc

/-- See clauseId_le_bool_total for the explicit-parens rationale. -/
private theorem crossRefKey_le_bool_total (a b : CrossRefScope) :
    (decide (crossRefKey a ≤ crossRefKey b) || decide (crossRefKey b ≤ crossRefKey a)) = true := by
  rcases String.le_total (crossRefKey a) (crossRefKey b) with h | h
  · rw [decide_eq_true_iff.mpr h]; rfl
  · rw [decide_eq_true_iff.mpr h]; simp

/-- Re-sorting an already crossRefKey-sorted list is a no-op.
    Uses List.sorted_mergeSort + List.mergeSort_of_sorted (Lean 4 core). -/
private theorem mergeSort_crossRefKey_idem (refs : List CrossRefScope) :
    (refs.mergeSort (fun a b => crossRefKey a ≤ crossRefKey b)).mergeSort
      (fun a b => crossRefKey a ≤ crossRefKey b) =
    refs.mergeSort (fun a b => crossRefKey a ≤ crossRefKey b) :=
  List.mergeSort_of_sorted
    (List.sorted_mergeSort crossRefKey_le_bool_trans crossRefKey_le_bool_total refs)

/-- Sort cross-references for canonical representation. -/
def normaliseCrossRefs (c : Clause) : Clause :=
  { c with crossRefs := c.crossRefs.mergeSort (fun a b => crossRefKey a ≤ crossRefKey b) }

theorem normaliseCrossRefs_idempotent (c : Clause) :
    normaliseCrossRefs (normaliseCrossRefs c) = normaliseCrossRefs c := by
  simp only [normaliseCrossRefs]
  congr 1
  exact mergeSort_crossRefKey_idem c.crossRefs

-- ============================================================
-- Full normalisation pass (composition of N1..N4)
-- ============================================================

/-- Full normalisation: apply all four passes in sequence.
    The passes commute because each targets a different field of Clause
    (voice, negation, exceptionStructure, crossRefs are disjoint). -/
def normalise (c : Clause) : Clause :=
  normaliseCrossRefs (normaliseExceptions (normaliseNegation (normaliseVoice c)))

/-- The full normalisation pass is idempotent.
    Proof: unfold all sub-passes, then let simp close each field
    using the per-field idempotence lemmas. The fields are disjoint
    so the lemmas apply independently. -/
theorem normalise_idempotent (c : Clause) :
    normalise (normalise c) = normalise c := by
  simp only [normalise, normaliseCrossRefs, normaliseExceptions, normaliseNegation, normaliseVoice,
             negation_normalise_idempotent, flattenExceptions_idempotent, mergeSort_crossRefKey_idem]

-- ============================================================
-- Provision-level and document-level normalisation
-- ============================================================

/-- Normalise every clause in a provision. -/
def normaliseProvision (p : Provision) : Provision :=
  { p with clauses := p.clauses.map normalise }

theorem normaliseProvision_idempotent (p : Provision) :
    normaliseProvision (normaliseProvision p) = normaliseProvision p := by
  simp [normaliseProvision, List.map_map, Function.comp, normalise_idempotent]

/-- Normalise every provision in an IR document. -/
def normaliseDocument (doc : IRDocument) : IRDocument :=
  { doc with provisions := doc.provisions.map normaliseProvision }

-- ============================================================
-- Stage-by-stage diff: compare before/after a normalisation pass
-- ============================================================

/-- A record of what changed during a single normalisation pass. -/
structure NormalisationDiff where
  clauseId      : String
  field         : String   -- which field changed
  before        : String
  after         : String
  deriving Repr

/-- Compute the diff for voice normalisation on a single clause. -/
def diffVoice (c : Clause) : Option NormalisationDiff :=
  if c.voice != Voice.active then
    some {
      clauseId := c.id
      field    := "voice"
      before   := toString (repr c.voice)
      after    := toString (repr Voice.active)
    }
  else none

/-- Compute the diff for negation normalisation on a single clause. -/
def diffNegation (c : Clause) : Option NormalisationDiff :=
  let n' := c.negation.normalise
  if n' != c.negation then
    some {
      clauseId := c.id
      field    := "negation"
      before   := toString (repr c.negation)
      after    := toString (repr n')
    }
  else none

/-- Compute the diff for exception flattening on a single clause. -/
def diffExceptions (c : Clause) : Option NormalisationDiff :=
  let es' := flattenExceptions c.exceptionStructure
  -- Compare by counting refs as a proxy for structural change
  let before_len := c.exceptionStructure.allRefs.length
  let after_len  := es'.allRefs.length
  if before_len != after_len then
    some {
      clauseId := c.id
      field    := "exceptionStructure"
      before   := s!"refs={before_len}"
      after    := s!"refs={after_len}"
    }
  else none

/-- Produce all diffs for a clause across all normalisation passes. -/
def diffClause (c : Clause) : List NormalisationDiff :=
  [diffVoice c, diffNegation c, diffExceptions c].filterMap id

/-- Produce diffs for every clause in a provision. -/
def diffProvision (p : Provision) : List NormalisationDiff :=
  p.clauses.foldl (fun acc c => acc ++ diffClause c) []

/-- Produce diffs for an entire IR document, annotated by provision. -/
def diffDocument (doc : IRDocument) : List NormalisationDiff :=
  doc.provisions.foldl (fun acc p => acc ++ diffProvision p) []

end LegalLean.IR.Normalise
