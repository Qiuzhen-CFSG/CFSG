module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Checks.Node000
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Checks.Node001
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Checks.Node002
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Checks.Node003
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Checks.Node004
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Certificate
import Mathlib.Tactic.IntervalCases

/-!
# The certified initial segment of the Fi23 seed program

The first two nodes are the literal subgroup generators, the next two their
inverses, and node four is the square of the first inverse. Its packed table
is checked on all 31671 letters. This is a complete sample of the finite
certificate route, including its application to subgroup membership.

Source: ATLAS F23G1-p31671B0 and `Links/source/seed-nodes.json`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds

theorem initial_steps (k : Nat) (hk : k < 5) : Equation table k (program k) := by
  interval_cases k
  · exact Node000.equation
  · exact Node001.equation
  · exact Node002.equation
  · exact Node003.equation
  · exact Node004.equation

/-- Actual subgroup realization of the checked sample, with no certificate premise. -/
theorem initial_realized (k : Nat) (hk : k < 5) : Realized (table k) :=
  realized_of_equations 5 program table
    (fun i hi => program_earlier i (Nat.lt_trans hi (by decide))) initial_steps k hk

/-- Subsequent certificate batches need not repeat the completed initial segment. -/
theorem steps_of_remaining
    (h : ∀ k, 5 ≤ k → k < 345 → Equation table k (program k)) : Steps := by
  intro k hk
  by_cases hi : k < 5
  · exact initial_steps k hi
  · exact h k (Nat.le_of_not_gt hi) hk

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
