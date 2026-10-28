module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.TwoInvolutionsSymmetricThree
public import Mathlib.GroupTheory.PGroup

/-!
# Pairs of involutions with singular displacement in O₄⁺(2)

An isometry preserving the two anisotropic planes and having only singular
displacement vectors fixes both planes pointwise. Every remaining involution
swaps the two planes, with inverse S₃ entries. The product of two such swaps
has order dividing two or three; a kernel-checked calculation involves just
the 36 pairs of S₃ entries. In the former case the actors commute and generate
a two-group; in the latter their actual generated subgroup is S₃.

The singular-displacement hypothesis includes the identity actor and requires
neither a fixed-space order nor a displacement-rank assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.5(6),
via the actual quaternion central-product square quotient in the original
conjugate pair. The source action, displacement-square and action-kernel
transport are supplied by the ConjugatePairSeed orthogonal-action consumer.
-/

@[expose] public section
open Subgroup
namespace BinaryFourPlus

/-- The actual quadratic form vanishes on every displacement. -/
def SingularDisplacements (w : Wreath) : Prop :=
  ∀ v : V, q ((wreathToIsometry w).val v - v) = 0

private theorem plane_anisotropic (v : Plane) (hv : planeQ v = 0) : v = 0 := by
  have h : ∀ v : Plane, planeQ v = 0 → v = 0 := by decide +kernel
  exact h v hv

theorem eq_one_of_singular_preserving (w : Wreath) (hw : SingularDisplacements w)
    (hr : w.right = 1) : w = 1 := by
  have h0 (v : Plane) : planeLinear (w.left 1) v = v := by
    have h := hw (v,0)
    rw [wreathToIsometry_apply, if_pos hr] at h
    have hq : planeQ (planeLinear (w.left 1) v - v) = 0 := by
      simpa only [Prod.mk_sub_mk, map_zero, sub_zero, q_split, add_zero] using h
    exact sub_eq_zero.mp (plane_anisotropic _ hq)
  have h1 (v : Plane) : planeLinear (w.left swapIndex) v = v := by
    have h := hw (0,v)
    rw [wreathToIsometry_apply, if_pos hr] at h
    have hq : planeQ (planeLinear (w.left swapIndex) v - v) = 0 := by
      simpa only [Prod.mk_sub_mk, map_zero, sub_zero, q_split, zero_add] using h
    exact sub_eq_zero.mp (plane_anisotropic _ hq)
  apply RegularWreathProduct.ext
  · funext i
    have hi : i = 1 ∨ i = swapIndex := by revert i; decide +kernel
    apply planeLinear_injective
    change planeLinear (w.left i) = planeLinear 1
    rw [planeLinear_one]
    apply LinearEquiv.ext
    intro v
    rcases hi with rfl | rfl
    · exact h0 v
    · exact h1 v
  · exact hr

private def swapElement (p : Equiv.Perm (Fin 3)) : Wreath :=
  ⟨fun i => if i = 1 then p else p⁻¹, swapIndex⟩

private theorem swap_form (w : Wreath) (hw : w^2=1) (hr : w.right ≠ 1) :
    w = swapElement (w.left 1) := by
  have hs : w.right = swapIndex := (by decide : ∀ i : C2, i=1 ∨ i=swapIndex) w.right |>.resolve_left hr
  have hmul := congrArg (fun x : Wreath => x.left 1) hw
  have hinv : w.left swapIndex = (w.left 1)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa only [pow_two, RegularWreathProduct.mul_left, Pi.mul_apply, hs,
      swapIndex_inv, mul_one, RegularWreathProduct.one_left, Pi.one_apply] using hmul
  apply RegularWreathProduct.ext
  · funext i
    have hi : i = 1 ∨ i = swapIndex := by revert i; decide +kernel
    rcases hi with rfl | rfl <;> simp [swapElement, hinv]
  · exact hs

private theorem swap_product_relation (p r : Equiv.Perm (Fin 3)) :
    (swapElement p * swapElement r)^2=1 ∨ (swapElement p * swapElement r)^3=1 := by
  have h : ∀ p r : Equiv.Perm (Fin 3),
      (((swapElement p * swapElement r)^2).left = 1 ∧
        ((swapElement p * swapElement r)^2).right = 1) ∨
      (((swapElement p * swapElement r)^3).left = 1 ∧
        ((swapElement p * swapElement r)^3).right = 1) := by decide +kernel
  rcases h p r with h | h
  · exact Or.inl (RegularWreathProduct.ext h.1 h.2)
  · exact Or.inr (RegularWreathProduct.ext h.1 h.2)

theorem singular_involutions_product_relation (a b : Wreath) (ha : a^2=1) (hb : b^2=1)
    (hsa : SingularDisplacements a) (hsb : SingularDisplacements b) :
    (a*b)^2=1 ∨ (a*b)^3=1 := by
  by_cases har : a.right=1
  · rw [eq_one_of_singular_preserving a hsa har, one_mul]
    exact Or.inl hb
  by_cases hbr : b.right=1
  · rw [eq_one_of_singular_preserving b hsb hbr, mul_one]
    exact Or.inl ha
  rw [swap_form a ha har, swap_form b hb hbr]
  exact swap_product_relation _ _

private theorem two_group_of_involutions_square_product {G : Type*} [Group G] [Finite G]
    (a b : G) (ha : a^2=1) (hb : b^2=1) (hab : (a*b)^2=1) :
    IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup G) := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha)
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have hc : Commute a b := by
    have hh : (a*b)⁻¹=a*b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hab)
    rw [mul_inv_rev,hai,hbi] at hh
    exact hh.symm
  have hpa : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ha)
  have hpb : IsPGroup 2 (zpowers b) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hb)
  apply hpa.to_sup_of_normal_right' hpb
  apply le_trans _ (centralizer_le_normalizer (zpowers b : Set G))
  apply zpowers_le.mpr
  apply mem_centralizer_iff.mpr
  rintro _ ⟨n,rfl⟩
  exact (hc.zpow_right n).eq.symm

/-- Two involutive plus isometries with totally singular displacement generate
a two-group or an actual symmetric-three subgroup. Identity actors are allowed. -/
theorem singular_involutions_pair (a b : Wreath) (ha : a^2=1) (hb : b^2=1)
    (hsa : SingularDisplacements a) (hsb : SingularDisplacements b) :
    IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup Wreath) ∨
      Nonempty ((zpowers a ⊔ zpowers b : Subgroup Wreath) ≃* Equiv.Perm (Fin 3)) := by
  rcases singular_involutions_product_relation a b ha hb hsa hsb with h | h
  · exact Or.inl (two_group_of_involutions_square_product a b ha hb h)
  · by_cases he : a*b=1
    · exact Or.inl (two_group_of_involutions_square_product a b ha hb (by rw [he,one_pow]))
    · exact Or.inr (symmetricThree_of_involutions_product_three a b ha hb (orderOf_eq_prime h he))

/-- The non-two-group source pair is symmetric-three, with the original two
actors and their literal generated subgroup retained. -/
theorem symmetricThree_of_singular_involutions (a b : Wreath) (ha : a^2=1) (hb : b^2=1)
    (hsa : ∀ v : V, q ((wreathToIsometry a).val v-v)=0)
    (hsb : ∀ v : V, q ((wreathToIsometry b).val v-v)=0)
    (hn : ¬ IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup Wreath)) :
    Nonempty ((zpowers a ⊔ zpowers b : Subgroup Wreath) ≃* Equiv.Perm (Fin 3)) :=
  (singular_involutions_pair a b ha hb hsa hsb).resolve_left hn
end BinaryFourPlus
