module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.First.Reduction
import Mathlib.Tactic.FinCases

/-!
# All seven initial transitions at suffix letter 40

Five transitions are defining tree edges. The other two use the inverse of
an involutory target generator, whose packed table is definitionally the
source action. Each identity holds on all 31671 letters.
Source application: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First

theorem initial_step (a : Fin 7) (x : Fin 31671) :
    KernelUpperThird.packedForward a (representativeRun 0 x) =
      representativeRun (transitionForward a 0) (factorRun a 0 x) := by
  fin_cases a <;> rfl

/-- All defining edges and all initial transitions are already proved. -/
theorem step_of_remaining (a : Fin 7)
    (h : ∀ r : Fin 180, r ≠ 0 → treeEdge a r.val = false → ∀ x : Fin 31671,
      KernelUpperThird.packedForward a (representativeRun r x) =
        representativeRun (transitionForward a r) (factorRun a r x)) : Step a := by
  apply step_of_nontree
  intro r ht x
  by_cases hr : r = 0
  · subst r
    exact initial_step a x
  · exact h r hr ht x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First
