module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.WreathTwoThreeCore
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane

/-!
# Cubic Sylow fixed vectors in the binary plus four-space

The two independent cubic plane rotations lie in the characteristic three-core,
and hence in every Sylow three-subgroup. Their common fixed space is zero,
as verified on the sixteen vectors of the original wreath action.

Source application: Aschbacher--Smith, 14.3.18, printed pp.995--996.
-/

open Subgroup
namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private def axisCycle (side : Bool) : Wreath :=
  ⟨fun i => if (i=1)=side then cycle else 1,1⟩
private def eval (w : Wreath) (v : V) : V :=
  if w.right=1 then (planeLinear (w.left 1) v.1,planeLinear (w.left swapIndex) v.2)
  else (planeLinear (w.left 1) v.2,planeLinear (w.left swapIndex) v.1)
private theorem eval_eq (w : Wreath) (v : V) : eval w v=(wreathToIsometry w).val v :=
  (wreathToIsometry_apply w v).symm
private theorem axisCycle_cube (side : Bool) : axisCycle side^3=1 := by
  cases side <;> decide +kernel
private theorem core_quotient_two : IsPGroup 2 (Wreath ⧸ pCore 3 Wreath) := by
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := RegularWreathProduct.congr eSL (MulEquiv.refl C2)
  exact Theory.GroupTheory.WreathTwoResidual.threeCore_quotient_two.of_equiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 3 e))
private theorem axisCycle_mem_core (side : Bool) : axisCycle side ∈ pCore 3 Wreath := by
  let f := QuotientGroup.mk' (pCore 3 Wreath)
  have hd : orderOf (f (axisCycle side)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow,axisCycle_cube,map_one])
  have hc := core_quotient_two.orderOf_coprime (by decide : Nat.Coprime 2 3)
    (f (axisCycle side))
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd))
private theorem fixed_table : ∀ v : V,
    eval (axisCycle true) v=v → eval (axisCycle false) v=v → v=0 := by
  decide +kernel

/-- The natural action of every Sylow three-subgroup has zero fixed space. -/
public theorem sylow_three_fixed_eq_zero (P : Sylow 3 Wreath) (v : V)
    (hfix : ∀ a ∈ (P : Subgroup Wreath), (wreathToIsometry a).val v=v) : v=0 := by
  have hc : pCore 3 Wreath ≤ P := pCore_isPGroup.le_sylow_of_normal P
  apply fixed_table v
  · rw [eval_eq]
    exact hfix _ (hc (axisCycle_mem_core true))
  · rw [eval_eq]
    exact hfix _ (hc (axisCycle_mem_core false))
end BinaryFourPlus
