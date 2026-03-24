/-
  LegalLean.Defeasible — Non-monotonic reasoning for legal rules.

  Legal reasoning is defeasible: a conclusion that holds given current
  evidence can be retracted by new evidence or a higher-priority rule.
  This is fundamentally non-monotonic — adding premises can REMOVE
  conclusions. Classical logic is monotonic; legal logic is not.

  Key reference: Lawsky, "A Logic for Statutes" (default logic approach).
  Also: Governatori's Defeasible Deontic Logic (DDL).

  Compatible with Lean 4 v4.24.0 (Aristotle's version).
-/

import LegalLean.Core

namespace LegalLean

/-- A defeasible conclusion: holds unless defeated.
    `DefeasiblyHolds P` means P is established by some rule,
    but could be retracted if a defeating rule applies.

    Note: no `deriving` — contains `EvidenceFor P` which has Prop-valued field. -/
structure DefeasiblyHolds (P : Prop) where
  /-- The rule that establishes this conclusion. -/
  supportingRule : String
  /-- The current evidence. -/
  evidence : EvidenceFor P
  /-- Rules that COULD defeat this conclusion (by ID). -/
  potentialDefeaters : List String
  /-- Whether any defeater is currently active. -/
  defeated : Bool

/-- Check whether a defeasible conclusion is currently undefeated. -/
def DefeasiblyHolds.holds {P : Prop} (d : DefeasiblyHolds P) : Prop :=
  d.defeated = false

/-- A default rule in the sense of Reiter's default logic:
    "If prerequisite holds AND justification is consistent, conclude consequent."
    Legal default: "If conditions met AND no exception applies, then obligation holds." -/
structure DefaultRule where
  id : String
  /-- The prerequisite that must be established. -/
  prerequisite : String
  /-- The justification that must be consistent (not defeated). -/
  justification : String
  /-- The consequent that follows. -/
  consequent : String
  /-- Priority for conflict resolution between defaults. -/
  priority : Priority
  deriving Repr

/-- A defeat relation between two rules.
    `Defeats r1 r2` means r1 can defeat r2's conclusion. -/
structure Defeats where
  defeater : String    -- rule ID
  defeated : String    -- rule ID
  reason : String      -- why this defeat relation holds
  /-- Whether defeat is strict (always wins) or defeasible (can itself be defeated). -/
  strict : Bool
  deriving Repr, BEq

end LegalLean
