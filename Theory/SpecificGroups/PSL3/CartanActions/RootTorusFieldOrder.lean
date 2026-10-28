module
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusControl

/-!
# Coefficient order detected by the graph-fixed root torus

A Borel-preserving linear-field-graph actor acts on diag(a,1,a⁻¹)
modulo the upper unipotent subgroup by its field factor. Iteration preserves
this formula. The odd root torus meets the unipotent two-group trivially,
so every power killing the actor also kills its coefficient action.

Source: Aschbacher--Smith 11.5.6(3), printed p.781. The opposition graph
fixes this literal root torus; the projective scalar kernel is retained.
-/

public section

open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions.BorelQuotient Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3.CartanActions.RootTorusControl
open scoped MatrixGroups
namespace Matrix.PSL3.CartanActions.RootTorusControl
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

theorem actor_rootTorus_pow (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (j : ℕ) (a : Fˣ) : ∃ u ∈ unipotent F,
      ((projectiveActor F m σ ε) ^ j) (rootTorus F a) =
        u * rootTorus F (Units.map (σ ^ j).toMonoidHom a) := by
  induction j with
  | zero =>
    refine ⟨1,one_mem _,?_⟩
    simp only [pow_zero,MulAut.one_apply,one_mul]
    congr 1
  | succ j ih =>
    obtain ⟨u,hu,he⟩ := ih
    obtain ⟨v,hv,hvE⟩ := actor_rootTorus_factor F m σ ε hU
      (Units.map (σ ^ j).toMonoidHom a)
    refine ⟨projectiveActor F m σ ε u * v, mul_mem ?_ hv, ?_⟩
    · rw [← hU]
      exact mem_map_of_mem _ hu
    · rw [pow_succ',MulAut.mul_apply,he,map_mul,hvE,mul_assoc]
      congr 2
      congr 1
      apply Units.ext
      rw [pow_succ']
      rfl
theorem actor_coefficient_pow {n j : ℕ} (hF : Nat.card F = 2 ^ n)
    (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (hj : projectiveActor F m σ ε ^ j = 1) : σ ^ j = 1 := by
  have hodd : Odd (Nat.card (rootTorus F).range) :=
    (units_odd F hF).of_dvd_nat (card_range_dvd (rootTorus F))
  have hd : Disjoint (unipotent F) (rootTorus F).range := by
    apply disjoint_of_coprime_natCard
    rw [card_unipotent,hF,← pow_mul]
    exact hodd.coprime_two_left.pow_left _
  have hfix (a : Fˣ) : Units.map (σ ^ j).toMonoidHom a = a := by
    obtain ⟨u,hu,he⟩ := actor_rootTorus_pow F m σ ε hU j a
    rw [hj,MulAut.one_apply] at he
    have hmem : rootTorus F a * (rootTorus F (Units.map (σ ^ j).toMonoidHom a))⁻¹ ∈
        unipotent F := by rw [he,mul_inv_cancel_right]; exact hu
    have hone := disjoint_def.mp hd hmem ((rootTorus F).range.mul_mem
      ⟨a,rfl⟩ ((rootTorus F).range.inv_mem ⟨_,rfl⟩))
    exact ((rootTorus_injective F) (mul_inv_eq_one.mp hone)).symm
  ext a
  by_cases ha : a = 0
  · simp [ha]
  · exact congrArg Units.val (hfix (Units.mk0 a ha))
end Matrix.PSL3.CartanActions.RootTorusControl
