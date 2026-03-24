/-
  LegalLean.Solver — Generic defeasibility solver for lists of LegalRules.

  This module provides `solve : List (LegalRule α) → α → FormalisationBoundary Prop`,
  which consumes the `applicable`, `defeatedBy` and `priority` fields of each rule
  dynamically and returns a single `FormalisationBoundary Prop` for the given facts.

  Design principles:
  - Applicability filter: before defeat resolution, rules are filtered to those
    where `rule.applicable facts = true`.  Rules with the default
    `applicable := fun _ => true` always pass this filter (no existing behaviour
    changes).
  - Defeat is determined by ID membership: rule r is defeated if any rule d in the
    active set has d.id ∈ r.defeatedBy (i.e., r explicitly declares d as a defeater).
    This mirrors the `defeatedBy : List String` field semantics in `LegalRule`.
  - Among undefeated rules, the one with the highest `priority.level` wins.
  - Ties (same priority level) resolve to `boundary` — the solver cannot decide,
    a human authority must determine which rule prevails.
  - If no applicable rules exist, the result is `boundary` (no applicable rule = human
    must decide), encoding Hart's open texture as the default state.

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
-/

import LegalLean.Core
import LegalLean.Defeasible

namespace LegalLean

-- ============================================================
-- Defeat checking: purely structural, operates on rule metadata
-- ============================================================

/-- Check whether rule `r` is defeated by any rule in `activeRules`.
    A rule is defeated if its `defeatedBy` list contains the id of some
    active rule.  This uses the rule's own declaration of potential defeaters —
    the authoring jurist annotates each rule with which rules can override it.

    Complexity: O(n × k) where n = |activeRules|, k = |r.defeatedBy|. -/
def isDefeated {α : Type} (r : LegalRule α) (activeRules : List (LegalRule α)) : Bool :=
  activeRules.any (fun d => r.defeatedBy.contains d.id)

/-- Filter a list of rules to those not defeated by any other rule in the same list.
    This is the "stable set" [set of mutually consistent, undefeated rules] for a
    given rule corpus.

    Note: defeat is asymmetric — if r.defeatedBy contains d.id, then r is
    defeated by d, but d is not necessarily defeated by r. -/
def undefeatedRules {α : Type} (rules : List (LegalRule α)) : List (LegalRule α) :=
  rules.filter (fun r => !isDefeated r rules)

-- ============================================================
-- Priority selection: deterministic tie-breaking
-- ============================================================

/-- Find the rule with the maximum `priority.level` in a list.
    Returns `none` for an empty list.
    If two rules share the same level, the FIRST one in list order is returned
    (preserving predictable, deterministic behaviour for the solver). -/
def maxPriorityRule {α : Type} : List (LegalRule α) → Option (LegalRule α)
  | []      => none
  | r :: rs =>
    match maxPriorityRule rs with
    | none   => some r
    | some s => if r.priority.level ≥ s.priority.level then some r else some s

/-- Check whether all rules in a list share the same `priority.level`.
    Used to detect genuine ties that cannot be resolved without human judgment. -/
def allSamePriority {α : Type} (rules : List (LegalRule α)) : Bool :=
  match rules with
  | []      => true
  | r :: rs => rs.all (fun s => r.priority.level == s.priority.level)

-- ============================================================
-- The generic solver
-- ============================================================

/-- `solve rules facts` runs the defeasibility solver over `rules` applied to `facts`.

    Algorithm:
    0. Filter the corpus to rules where `applicable facts = true`.  Rules that
       are not applicable to the current facts are excluded before defeat
       resolution, making the solver fact-sensitive [context-aware].
    1. No applicable rules in corpus → `boundary` (nothing to decide on; human must determine)
    2. No undefeated applicable rules → `boundary` (all defeated; open texture)
    3. Exactly one undefeated applicable rule → `formal` wrapping that rule's conclusion
    4. Multiple undefeated applicable rules, all same priority → `boundary` (tie; human decides)
    5. Multiple undefeated applicable rules, different priorities → `formal` wrapping the
       highest-priority rule's conclusion on `facts`

    The `authority` used in `boundary` cases is a placeholder string; callers
    should compose this with domain-specific authority metadata where needed.

    Note: rules with `applicable := fun _ => true` (the default) are never
    filtered out, so all existing callers without explicit `applicable` fields
    behave identically to before. -/
def solve {α : Type} (rules : List (LegalRule α)) (facts : α)
    : FormalisationBoundary Prop :=
  -- Step 0: filter to fact-applicable rules before any defeat resolution.
  let applicable := rules.filter (fun r => r.applicable facts)
  match applicable with
  | [] =>
      FormalisationBoundary.boundary
        "No rules in corpus — human authority must determine applicable law"
        Authority.irsTaxCourt
  | _ =>
      let active := undefeatedRules applicable
      match active with
      | [] =>
          FormalisationBoundary.boundary
            "All rules have been defeated — open texture; human determination required"
            Authority.irsTaxCourt
      | [r] =>
          FormalisationBoundary.formal (r.conclusion facts)
      | _ =>
          if allSamePriority active then
            FormalisationBoundary.boundary
              ("Priority tie among undefeated rules: " ++
               String.intercalate ", " (active.map (fun r => r.id)) ++
               " — human authority must resolve")
              Authority.irsTaxCourt
          else
            match maxPriorityRule active with
            | none =>
                -- unreachable: active is non-empty, so maxPriorityRule returns some
                FormalisationBoundary.boundary
                  "Solver internal error: maxPriorityRule returned none on non-empty list"
                  Authority.irsTaxCourt
            | some winner =>
                FormalisationBoundary.formal (winner.conclusion facts)

-- ============================================================
-- Theorems: structural properties of the SOLVER itself
-- (not of any specific rule corpus)
-- ============================================================

/-- Theorem S1: Empty corpus always yields a boundary.
    If no rules apply, the solver cannot make a formal determination —
    it must defer to human authority.  This is the type-level encoding
    of Hart's thesis: absent positive law, open texture prevails.

    This is the strongest guarantee we can make about solver behaviour
    without any domain-specific knowledge. -/
theorem solve_empty_corpus_is_boundary {α : Type} (facts : α) :
    ∃ reason auth,
      solve ([] : List (LegalRule α)) facts =
        FormalisationBoundary.boundary reason auth := by
  exact ⟨_, _, rfl⟩

/-- Theorem S2: A single applicable, undefeated rule with no defeaters yields `formal`.
    When exactly one rule exists, it is applicable to `facts`, and it cannot be
    defeated (defeatedBy = []), the solver returns `formal (rule.conclusion facts)`.

    This proves that the solver is not overly conservative — it does not
    retreat to `boundary` when the answer is determinable.

    Note: the `h_applicable` hypothesis is required by the `applicable`-filter
    in `solve`.  Rules with the default `applicable := fun _ => true` always
    satisfy this (the hypothesis holds by `rfl` for such rules). -/
theorem solve_single_undefeated_rule_is_formal
    {α : Type} (r : LegalRule α) (facts : α)
    (h_no_defeaters : r.defeatedBy = [])
    (h_applicable : r.applicable facts = true) :
    solve [r] facts = FormalisationBoundary.formal (r.conclusion facts) := by
  simp [solve, undefeatedRules, isDefeated, h_no_defeaters, h_applicable]

/-- Theorem S3: If a rule's defeatedBy list is empty, isDefeated returns false
    regardless of what other rules are present.
    This is a lemma [auxiliary result] supporting the monotonicity theorem below. -/
theorem isDefeated_false_of_empty_defeatedBy
    {α : Type} (r : LegalRule α) (rules : List (LegalRule α))
    (h : r.defeatedBy = []) :
    isDefeated r rules = false := by
  simp [isDefeated, h]

/-- Theorem S4: undefeatedRules is monotone [output cannot shrink] in one direction —
    removing a rule from the corpus cannot cause a previously-defeated rule to become
    undefeated (because fewer defeaters can only REDUCE defeat, not increase it).

    Stated contrapositively: if a rule r is in `undefeatedRules rules`,
    and we REMOVE a rule from `rules` to get `rules'`, then r may or may not
    appear in `undefeatedRules rules'` — we cannot say in general.

    What we CAN prove (the useful direction): if a rule is defeated in a
    sub-corpus, it is still defeated when we add more rules.

    Formally: isDefeated r smaller → isDefeated r (smaller ++ extra). -/
theorem isDefeated_monotone_in_rules
    {α : Type} (r : LegalRule α) (smaller extra : List (LegalRule α))
    (h : isDefeated r smaller = true) :
    isDefeated r (smaller ++ extra) = true := by
  simp only [isDefeated, List.any_eq_true] at *
  obtain ⟨d, hd_mem, hd_contains⟩ := h
  exact ⟨d, List.mem_append_left extra hd_mem, hd_contains⟩

/-- Theorem S5: The solver result is `formal` only when there is at least one
    undefeated applicable rule in the corpus (contrapositive: no such rules → boundary).

    This formalises the intuition that `formal` outcomes require positive legal
    authority — the type system cannot manufacture a conclusion from nothing.

    Note: with the `applicable` predicate, "undefeated" is relative to the
    applicable sub-corpus.  We state this in terms of the filtered list. -/
theorem solve_formal_implies_nonempty_undefeated
    {α : Type} (rules : List (LegalRule α)) (facts : α) (P : Prop)
    (h : solve rules facts = FormalisationBoundary.formal P) :
    undefeatedRules (rules.filter (fun r => r.applicable facts)) ≠ [] := by
  simp only [solve] at h
  by_cases h_app : rules.filter (fun r => r.applicable facts) = []
  · simp [h_app] at h
  · by_cases h_und : undefeatedRules (rules.filter (fun r => r.applicable facts)) = []
    · -- undefeated = [] → solver returned boundary, contradicts h
      cases h_cases : (rules.filter (fun r => r.applicable facts)) with
      | nil => exact absurd h_cases h_app
      | cons hd tl =>
        rw [h_cases] at h h_und
        simp [h_und] at h
    · exact h_und

/-- Theorem S6: Solver is deterministic [same inputs → same output].
    In Lean 4, all pure functions are definitionally deterministic, so this is
    trivially true by reflexivity.  We state it explicitly for documentation:
    the solver has no hidden state, randomness, or external oracle calls. -/
theorem solve_is_deterministic
    {α : Type} (rules : List (LegalRule α)) (facts : α) :
    solve rules facts = solve rules facts :=
  rfl

end LegalLean
