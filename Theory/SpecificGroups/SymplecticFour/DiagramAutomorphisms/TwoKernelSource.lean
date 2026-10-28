module
public import Theory.GroupTheory.CyclicTwoKernel
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource

/-!
# The order-two kernel test for a symplectic outer action

When the field exponent is even, an involution in the symplectic outer group
acts nontrivially on either preserved rank-one Levi quotient. Thus a two-group
whose involutions act inner on those quotients, and whose outer kernel has
order two, must be cyclic. This is the outer-action step of 2.4.24(2).
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open ExceptionalGraph InvolutionNormalForms
variable {F P : Type*} [Field F] [Finite F] [CharP F 2] [Group P] [Finite P]
/-- The source involution restriction contradicts a noncyclic two-group
acting on the symplectic component with outer kernel of order two. -/
theorem cyclic_of_outer_kernel_two_and_local_involutions
    {m : ℕ} (hcard : Nat.card F=2^m) (hm : 1<m) (heven : Even m)
    (hP : IsPGroup 2 P) (α : P →* MulAut (Sp F))
    (hker : Nat.card ((QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp α).ker=2)
    (hloc : ∀ t : P, orderOf t=2 →
      QuotientGroup.mk' (MulAut.innerSubgroup (Sp F)) (α t) ≠ 1 →
      (∃ h : pointLocal.map (α t).toMonoidHom = pointLocal,
        pointSL2Action hcard hm (α t) h ∈
          MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (∃ h : planeLocal.map (α t).toMonoidHom = planeLocal,
        planeSL2Action hcard hm (α t) h ∈
          MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) F))) : IsCyclic P := by
  let : IsCyclic (MulAut.Outer (Sp F)) := outer_cyclic hcard hm
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp α
  apply hP.isCyclic_of_involutions_in_two_kernel f hker
  intro t ht
  by_contra hne
  have ho : orderOf (f t)=2 := orderOf_eq_prime
    (by rw [←map_pow,show t^2=1 from ht ▸ pow_orderOf_eq_one t,map_one]) hne
  rcases hloc t ht hne with ⟨h,hinner⟩ | ⟨h,hinner⟩
  · exact outer_involution_pointSL2Action_not_inner hcard hm heven (α t) ho h hinner
  · exact outer_involution_planeSL2Action_not_inner hcard hm heven (α t) ho h hinner
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

