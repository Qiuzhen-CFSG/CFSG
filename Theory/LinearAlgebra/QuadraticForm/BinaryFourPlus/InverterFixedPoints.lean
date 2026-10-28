module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.LinearAlgebra.Dimension.Finite
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane
import Mathlib.Tactic

/-!
# Fixed vectors of the full cubic-residual inverter

The two independent cubic plane rotations belong to the two-residual. A
kernel-checked calculation on the seventy-two wreath actors and sixteen
vectors shows that every involution inverting both rotations fixes exactly
four vectors. Hence an involution inverting the whole residual moves some
vector of every subspace of dimension at least three.

The coordinate consumer retains an arbitrary original linear action and
marked subspace through an explicit intertwining equality. No choice of a
new subspace or action is involved.

Source application: Aschbacher--Smith, 14.3.15, printed p.994, the movement
of the original three-dimensional hat-space above the center-point case.
-/

open Subgroup Module
namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm
private def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private def axisCycle (side : Bool) : Wreath :=
  ⟨fun i=>if (i=1) = side then cycle else 1,1⟩
private def eval (w : Wreath) (v : V) : V :=
  if w.right=1 then (planeLinear (w.left 1) v.1,planeLinear (w.left swapIndex) v.2)
  else (planeLinear (w.left 1) v.2,planeLinear (w.left swapIndex) v.1)
private theorem eval_eq (w : Wreath) (v : V) : eval w v=(wreathToIsometry w).val v :=
  (wreathToIsometry_apply w v).symm
private theorem axisCycle_cube (side : Bool) : axisCycle side^3=1 := by
  cases side <;> decide +kernel
private theorem axisCycle_mem_residual (side : Bool) : axisCycle side∈pResidual 2 Wreath :=
  mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (axisCycle_cube side)))
private theorem inverter_table : ∀ r : Wreath, r^2=1 →
    (∀ side : Bool, r*axisCycle side*r⁻¹=(axisCycle side)⁻¹) →
      Fintype.card {v : V // eval r v=v}=4 := by
  decide +kernel

/-- An involution inverting the entire cubic residual fixes exactly four
vectors in the actual plus-four representation. -/
public theorem residual_inverter_fixed_card (r : Wreath) (hr : orderOf r=2)
    (hinv : ∀ x∈pResidual 2 Wreath, r*x*r⁻¹=x⁻¹) :
    Nat.card {v : V // (wreathToIsometry r).val v=v}=4 := by
  have hr2 : r^2=1 := by simpa only [hr] using pow_orderOf_eq_one r
  simpa only [Nat.card_eq_fintype_card,eval_eq] using
    inverter_table r hr2 (fun side => hinv _ (axisCycle_mem_residual side))

/-- The inverter cannot fix pointwise a subspace of dimension at least three. -/
public theorem residual_inverter_moves_of_finrank_ge_three
    (r : Wreath) (hr : orderOf r=2)
    (hinv : ∀ x∈pResidual 2 Wreath, r*x*r⁻¹=x⁻¹)
    (S : Submodule (ZMod 2) V) (hd : 3≤finrank (ZMod 2) S) :
    ∃ v∈S, (wreathToIsometry r).val v≠v := by
  classical
  by_contra! hfix
  let f : S → {v : V // (wreathToIsometry r).val v=v} := fun v=>⟨v,hfix v v.property⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun x : {v : V // (wreathToIsometry r).val v=v} => x.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [residual_inverter_fixed_card r hr hinv,
    Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hc
  have hh : 8≤2^finrank (ZMod 2) S :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hd
  omega

/-- Minimal transport consumer: the original marked subspace is moved
under any coordinates intertwining the given actor with the inverter. -/
public theorem residual_inverter_moves_in_coordinates
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : W≃ₗ[ZMod 2] V) (a : W→ₗ[ZMod 2] W)
    (r : Wreath) (hr : orderOf r=2)
    (hinv : ∀ x∈pResidual 2 Wreath, r*x*r⁻¹=x⁻¹)
    (ha : ∀ v, e (a v)=(wreathToIsometry r).val (e v))
    (S : Submodule (ZMod 2) W) (hd : 3≤finrank (ZMod 2) S) :
    ∃ v∈S, a v≠v := by
  have hd' : 3≤finrank (ZMod 2) (S.map e.toLinearMap) := by
    rw [LinearEquiv.finrank_map_eq]
    exact hd
  obtain ⟨v,⟨w,hw,he⟩,hm⟩ := residual_inverter_moves_of_finrank_ge_three r hr hinv
    (S.map e.toLinearMap) hd'
  refine ⟨w,hw,?_⟩
  intro hh
  apply hm
  rw [←he]
  exact (ha w).symm.trans (congrArg e hh)
end BinaryFourPlus
