module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Reduction
import Mathlib.Tactic.FinCases

/-!
# Five exact initial transitions

Four initial transitions are tree edges. The initial transition for generator 2
uses the inverse of packed target generator 2; their point functions agree by
definitional reduction of the exact tables. These five identities hold on all
31671 letters. The sixth initial transition, for generator 4, has a nonempty
factor word and remains part of the general transition obligation.

The row-extension theorem below consumes these identities when certifying the
remaining representatives. Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird

theorem initial_step (a : Fin 6) (ha : a ≠ 4) (x : Fin 31671) :
    secondMap a (representativeRun 0 x) =
      representativeRun (transitionForward a 0) (factorRun a 0 x) := by
  fin_cases a
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim (ha rfl)
  · rfl

/-- Five rows need only their noninitial identities after the checked initial step. -/
theorem step_of_noninitial (a : Fin 6) (ha : a ≠ 4)
    (h : ∀ r : Fin 693, r ≠ 0 → ∀ x : Fin 31671,
      secondMap a (representativeRun r x) =
        representativeRun (transitionForward a r) (factorRun a r x)) : Step a := by
  intro r x
  by_cases hr : r = 0
  · subst r
    exact initial_step a ha x
  · exact h r hr x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird
