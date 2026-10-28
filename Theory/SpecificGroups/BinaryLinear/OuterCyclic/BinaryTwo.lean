module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The natural binary plane for the derived linear group

The actual commutator subgroup of GL₂(2) consists of the identity and two
cubic matrices. An explicit commutator cycles the three nonzero vectors,
so the derived actor is transitive on them. Its automorphisms either fix
that generator or invert it; the coordinate swap implements inversion.
Both conclusions concern the natural matrix action, transported through
`slEquivLinear`, rather than an identification based only on group order.

The finite checks range over the sixteen binary 2-by-2 matrices and their
six determinant-one members, and are checked by the kernel. They supply
the cyclic-three case in the natural-module argument of Aschbacher–Smith,
combined manuscript of 1 March 2004, Lemma 12.8.5(1), printed p.850
(PDF p.867).
-/

@[expose] public section

open scoped MatrixGroups commutatorElement
open Subgroup
namespace BinaryLinear.OuterCyclic.BinaryTwo

private def swapSL : SL(2, ZMod 2) := ⟨!![0,1;1,0], by decide⟩
private def shearSL : SL(2, ZMod 2) := ⟨!![1,1;0,1], by decide⟩
private def cubicSL : SL(2, ZMod 2) := ⟨!![1,1;1,0], by decide⟩

private theorem cubicSL_commutator : ⁅swapSL, shearSL⁆ = cubicSL := by decide +kernel

private theorem cubicSL_cases : ∀ x : SL(2, ZMod 2), x ^ 3 = 1 →
    x = 1 ∨ x = cubicSL ∨ x = cubicSL ^ 2 := by decide +kernel

private theorem cubicSL_mul : ∀ x y : SL(2, ZMod 2),
    x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1 := by decide +kernel

private theorem commutator_cube : ∀ x y : SL(2, ZMod 2), ⁅x,y⁆ ^ 3 = 1 := by decide +kernel

private def cubicSubgroup : Subgroup SL(2, ZMod 2) where
  carrier := {x | x ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := cubicSL_mul _ _
  inv_mem' := by
    intro x hx
    change x ^ 3 = 1 at hx
    change x⁻¹ ^ 3 = 1
    rw [inv_pow, hx, inv_one]

private noncomputable def cubic : commutator (LinearGroup 2) :=
  ⟨slEquivLinear 2 cubicSL, by
    rw [← cubicSL_commutator, map_commutatorElement]
    exact commutator_mem_commutator (mem_top _) (mem_top _)⟩

private theorem derived_cases (g : commutator (LinearGroup 2)) :
    g = 1 ∨ g = cubic ∨ g = cubic ^ 2 := by
  have hle : commutator (LinearGroup 2) ≤
      cubicSubgroup.comap (slEquivLinear 2).symm.toMonoidHom := by
    apply commutator_le.mpr
    intro a _ b _
    change ((slEquivLinear 2).symm ⁅a,b⁆) ^ 3 = 1
    rw [map_commutatorElement]
    exact commutator_cube _ _
  have hg := hle g.property
  rcases cubicSL_cases ((slEquivLinear 2).symm g) hg with h | h | h
  · left
    apply Subtype.ext
    have he := congrArg (slEquivLinear 2) h
    simpa only [MulEquiv.apply_symm_apply, map_one, OneMemClass.coe_one] using he
  · right; left
    apply Subtype.ext
    exact (slEquivLinear 2).apply_symm_apply g |>.symm.trans (congrArg (slEquivLinear 2) h)
  · right; right
    apply Subtype.ext
    have he := congrArg (slEquivLinear 2) h
    simpa only [MulEquiv.apply_symm_apply, map_pow, SubgroupClass.coe_pow, cubic] using he

private theorem cubic_ne_one : cubic ≠ 1 := by
  intro h
  have he : slEquivLinear 2 cubicSL = slEquivLinear 2 1 := by
    simpa only [map_one, OneMemClass.coe_one, cubic] using congrArg Subtype.val h
  exact (by decide : cubicSL ≠ 1) ((slEquivLinear 2).injective he)

/-- The derived subgroup of GL₂(2) is transitive on the three nonzero vectors. -/
theorem derived_transitive_nonzero {v w : Space 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : commutator (LinearGroup 2), g.val v = w := by
  have h : ∀ v w : Space 2, v ≠ 0 → w ≠ 0 →
      v = w ∨ (cubicSL : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec v = w ∨
      ((cubicSL ^ 2 : SL(2,ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec v = w := by
    decide +kernel
  rcases h v w hv hw with h | h | h
  · exact ⟨1, h⟩
  · exact ⟨cubic, h⟩
  · refine ⟨cubic ^ 2, ?_⟩
    change (slEquivLinear 2 cubicSL ^ 2) v = w
    rw [← map_pow]
    exact h

private theorem swap_intertwines (v : Space 2) :
    slEquivLinear 2 swapSL (cubic.val v) = (cubic ^ 2).val (slEquivLinear 2 swapSL v) := by
  have h : swapSL * cubicSL = cubicSL ^ 2 * swapSL := by decide +kernel
  have he := congrArg (slEquivLinear 2) h
  simp only [map_mul, map_pow] at he
  exact congrArg (fun g : LinearGroup 2 => g v) he

private theorem swap_intertwines_square (v : Space 2) :
    slEquivLinear 2 swapSL ((cubic ^ 2).val v) =
      ((cubic ^ 2) ^ 2).val (slEquivLinear 2 swapSL v) := by
  have h : swapSL * cubicSL ^ 2 = (cubicSL ^ 2) ^ 2 * swapSL := by decide +kernel
  have he := congrArg (slEquivLinear 2) h
  simp only [map_mul, map_pow] at he
  exact congrArg (fun g : LinearGroup 2 => g v) he

/-- Every automorphism of GL₂(2)′ has a linear implementer on its natural plane.
The nonidentity automorphism is implemented by swapping the two coordinates. -/
theorem derived_automorphism_intertwiner (a : MulAut (commutator (LinearGroup 2))) :
    ∃ c : Space 2 ≃ₗ[ZMod 2] Space 2, ∀ g v, c (g.val v) = (a g).val (c v) := by
  have ha : a cubic ≠ 1 := fun h => cubic_ne_one (a.injective (h.trans a.map_one.symm))
  rcases derived_cases (a cubic) with h | h | h
  · exact (ha h).elim
  · refine ⟨LinearEquiv.refl (ZMod 2) (Space 2), ?_⟩
    intro g v
    rcases derived_cases g with rfl | rfl | rfl
    · rw [map_one]; rfl
    · rw [h]; rfl
    · rw [map_pow, h]; rfl
  · refine ⟨slEquivLinear 2 swapSL, ?_⟩
    intro g v
    rcases derived_cases g with rfl | rfl | rfl
    · rw [map_one]; rfl
    · rw [h]; exact swap_intertwines v
    · rw [map_pow, h]; exact swap_intertwines_square v

end BinaryLinear.OuterCyclic.BinaryTwo
