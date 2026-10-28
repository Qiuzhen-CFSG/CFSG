module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Components of A₅ and S₅

The alternating group A₅ is quasisimple. Perfectness puts every component of
S₅ in its index-two alternating subgroup; containment between components
then gives equality. The same component argument identifies every component
of A₅ with A₅ itself. The conclusions are actual multiplicative equivalences.

Source: Aschbacher–Smith 16.1.5(4) and its application in 16.1.7(3f),
combined manuscript of 1 March 2004, printed pp.1171–1172.
-/

public section
open Subgroup
namespace Theory.GroupTheory
private theorem a5_quasisimple : IsQuasisimple (alternatingGroup (Fin 5)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

/-- Every component of S₅ is isomorphic to its actual alternating subgroup. -/
theorem component_symmetric_five_equiv (K : Subgroup (Equiv.Perm (Fin 5)))
    (hK : IsComponent _ K) : Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  let := hK.2
  let := a5_quasisimple
  have hA : IsComponent (Equiv.Perm (Fin 5)) (alternatingGroup (Fin 5)) :=
    ⟨(inferInstance : (alternatingGroup (Fin 5)).Normal).isSubnormal, inferInstance⟩
  exact ⟨MulEquiv.subgroupCongr (hK.eq_of_le hA
    (le_of_isPerfect_of_index_eq_two K _ alternatingGroup.index_eq_two))⟩

/-- Every component of A₅ is the whole group, hence isomorphic to A₅. -/
theorem component_alternating_five_equiv (K : Subgroup (alternatingGroup (Fin 5)))
    (hK : IsComponent _ K) : Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  let := a5_quasisimple
  have ht : IsComponent (alternatingGroup (Fin 5)) ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv (topEquiv).symm⟩
  exact ⟨(MulEquiv.subgroupCongr (hK.eq_of_le ht le_top)).trans topEquiv⟩
end Theory.GroupTheory
