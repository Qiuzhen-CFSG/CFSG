module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# A finite group for the Sylow calculation

The concrete semidirect product C₈ ⋊ (Z/8)ˣ has order 32. Its marked
rotation, multiplier 5, and inversion satisfy the displayed relations
and generate the group. The marked subgroups specify the intended
inner-dihedral and permutation-induced parts for a later identification.

Source: the local Sylow calculations in Aschbacher–Smith, *The
Classification of Quasithin Groups*, printed pp.568–570. This module
constructs the calculation group only; applying its geometry to Aut(A₆)
requires a proved equivalence matching the marked subgroups.
-/

@[expose] public section

namespace AlternatingSix.ShadowLocal.Holomorph

def unitAction : (ZMod 8)ˣ →* MulAut (Multiplicative (ZMod 8)) where
  toFun u := {
    toFun := fun x => .ofAdd ((u : ZMod 8) * x.toAdd)
    invFun := fun x => .ofAdd (((u⁻¹ : (ZMod 8)ˣ) : ZMod 8) * x.toAdd)
    left_inv := fun x => by simp [← mul_assoc]
    right_inv := fun x => by simp [← mul_assoc]
    map_mul' := fun x y => by
      change Multiplicative.ofAdd (_ * (x.toAdd + y.toAdd)) =
        Multiplicative.ofAdd (_ * x.toAdd + _ * y.toAdd)
      rw [mul_add] }
  map_one' := by ext x; simp
  map_mul' u v := by ext x; simp [mul_assoc]

abbrev Model := Multiplicative (ZMod 8) ⋊[unitAction] (ZMod 8)ˣ

instance instFintypeModel : Fintype Model :=
  Fintype.ofEquiv (Multiplicative (ZMod 8) × (ZMod 8)ˣ) SemidirectProduct.equivProd.symm

def rotation : Model := SemidirectProduct.inl (.ofAdd 1)
def five : (ZMod 8)ˣ := ⟨5, 5, by decide, by decide⟩
def transposition : Model := SemidirectProduct.inr five
def reflection : Model := SemidirectProduct.inr (-1)

def innerD : Subgroup Model := Subgroup.closure {rotation ^ 2, reflection}
def natural : Subgroup Model := Subgroup.closure {rotation ^ 2, transposition, reflection}
def cyclicFour : Subgroup Model := Subgroup.zpowers (rotation ^ 2)
def transpositionSubgroup : Subgroup Model := Subgroup.zpowers transposition

theorem card_model : Nat.card Model = 32 := by
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hu : Fintype.card (ZMod 8)ˣ = 4 := by decide +kernel
  simp [hu]

theorem rotation_order : orderOf rotation = 8 := by
  rw [rotation, orderOf_injective _ SemidirectProduct.inl_injective]
  exact ZMod.addOrderOf_one 8

theorem transposition_sq : transposition ^ 2 = 1 := by
  decide +kernel

theorem reflection_sq : reflection ^ 2 = 1 := by
  decide +kernel

theorem transposition_rotation :
    transposition * rotation * transposition⁻¹ = rotation ^ 5 := by
  decide +kernel

theorem reflection_rotation :
    reflection * rotation * reflection⁻¹ = rotation⁻¹ := by
  decide +kernel

theorem transposition_reflection :
    transposition * reflection = reflection * transposition := by
  decide +kernel

theorem normal_form (x : Model) :
    ∃ (i : Fin 8) (j k : Fin 2),
      x = rotation ^ i.val * transposition ^ j.val * reflection ^ k.val := by
  revert x
  decide +kernel

theorem generated : Subgroup.closure {rotation, transposition, reflection} = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, j, k, rfl⟩ := normal_form x
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

end AlternatingSix.ShadowLocal.Holomorph
