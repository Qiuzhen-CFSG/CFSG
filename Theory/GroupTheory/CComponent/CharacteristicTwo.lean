module

public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# A local C-component in characteristic two is not quasisimple

A quasisimple subnormal subgroup lies in the generalized Fitting subgroup.
When F* is a two-group this would make the component solvable, contradicting
its nontrivial perfectness. This elementary distinction between ordinary
components and C-components is used in the quasisimple smaller-group branch
of Aschbacher–Smith A.3.12 and C.5.13, printed pp.47–48,163.
-/

public section
open Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsCComponent.not_isQuasisimple_of_characteristic_two
    {B : Subgroup G} (hB : B.IsCComponent)
    (hG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) : ¬ IsQuasisimple B := by
  intro hq
  have hle : B ≤ pCore 2 G := by
    rw [← generalizedFitting_eq_pCore_of_selfCentralizing 2 hG]
    exact component_le_generalizedFitting G B ⟨hB.subnormal, hq⟩
  let := pCore_isNilpotent (p := 2) (G := G)
  exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := inclusion hle) (inclusion_injective hle))

end Subgroup
