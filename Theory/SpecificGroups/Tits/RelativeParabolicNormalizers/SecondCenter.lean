module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondCenterCertificate
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# A normal two-subgroup of the second Tits parabolic

The words r5 and s1*s2*s3² lie in the certified Sylow subgroup. The
checked generator actions show that their generated subgroup is normal
in the second parabolic. It is therefore contained in that parabolic's
actual two-core, supplying the projection-core membership needed for
Aschbacher–Smith 2.3.9(7), printed p.526.

Its characteristic property in the Sylow subgroup and its full ambient
normalizer are separate obligations. No parabolic core order is used.
Source: Parrott (1972), p.683, with the existing Atlas marking.
-/

@[expose] public section

namespace Tits.RelativeParabolicNormalizers
open Subgroup ExceptionalParabolics
local notation "r8" => atlas1600ParrottAssignment ParrottGenerator.r8
local notation "s1" => atlas1600ParrottAssignment ParrottGenerator.s1
local notation "s2" => atlas1600ParrottAssignment ParrottGenerator.s2
local notation "s3" => atlas1600ParrottAssignment ParrottGenerator.s3

def secondCenterMate : Atlas1600Group := s1 * s2 * s3 ^ 2
def secondCenter : Subgroup Atlas1600Group :=
  zpowers atlas1600R5 ⊔ zpowers secondCenterMate

private theorem mate_mem_sylow : secondCenterMate ∈ S := by
  have he : atlas1600SylowTwoNormalForm 11 = secondCenterMate := by
    norm_num [atlas1600SylowTwoNormalForm_eq, secondCenterMate]
  rw [← he]
  exact atlas1600SylowTwoNormalForm_mem 11

theorem secondCenter_le_sylow : secondCenter ≤ S :=
  sup_le (zpowers_le.mpr atlas1600R5_mem_sylowTwo) (zpowers_le.mpr mate_mem_sylow)

theorem secondCenter_isPGroup : IsPGroup 2 secondCenter :=
  (atlas1600SylowTwo.isPGroup'.to_le (by simpa only [atlas1600SylowTwo_coe] using secondCenter_le_sylow))

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_inv (x : Atlas1600Group) : (x⁻¹).val = x.val⁻¹ := rfl
private theorem val_pow (x : Atlas1600Group) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl
private theorem r5_val : atlas1600R5.val = SecondCenterCertificate.x := by
  simp only [atlas1600R5_eq, val_mul, val_pow, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation, SecondCenterCertificate.x]
private theorem mate_val : secondCenterMate.val = SecondCenterCertificate.y := by
  simp only [secondCenterMate, val_mul, val_pow, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation, SecondCenterCertificate.y]

private theorem normalizes_of_generator_images (g : Atlas1600Group)
    (hx : g * atlas1600R5 * g⁻¹ ∈ secondCenter)
    (hy : g * secondCenterMate * g⁻¹ ∈ secondCenter) :
    g ∈ normalizer (secondCenter : Set Atlas1600Group) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [secondCenter, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hy)
  · rw [card_map_of_injective (MulAut.conj g).injective]

private theorem r5_mem_secondCenter : atlas1600R5 ∈ secondCenter :=
  (show zpowers atlas1600R5 ≤ secondCenter from le_sup_left) (mem_zpowers _)
private theorem mate_mem_secondCenter : secondCenterMate ∈ secondCenter :=
  (show zpowers secondCenterMate ≤ secondCenter from le_sup_right) (mem_zpowers _)

private theorem reflection_normalizes : r8 ∈ normalizer (secondCenter : Set Atlas1600Group) := by
  have hx : r8 * atlas1600R5 * r8⁻¹ = secondCenterMate := by
    apply Subtype.ext
    simpa only [val_mul, val_inv, r5_val, mate_val, atlas1600ParrottAssignment_val,
      Atlas1600ParrottData.permutation] using SecondCenterCertificate.reflection_x
  have hy : r8 * secondCenterMate * r8⁻¹ = atlas1600R5 := by
    apply Subtype.ext
    simpa only [val_mul, val_inv, r5_val, mate_val, atlas1600ParrottAssignment_val,
      Atlas1600ParrottData.permutation] using SecondCenterCertificate.reflection_y
  apply normalizes_of_generator_images r8
  · rw [hx]; exact mate_mem_secondCenter
  · rw [hy]; exact r5_mem_secondCenter

private theorem mate_image_mem (i : Fin 8) (g : Atlas1600Group)
    (hg : g.val = Atlas1600SylowTwoCenterCertificate.generator i) :
    g * secondCenterMate * g⁻¹ ∈ secondCenter := by
  have he : g * secondCenterMate * g⁻¹ =
      if i = 7 then atlas1600R5 * secondCenterMate else secondCenterMate := by
    apply Subtype.ext
    rw [val_mul, val_mul, val_inv, mate_val, hg]
    have hc := SecondCenterCertificate.sylow_y i
    split_ifs with hi
    · simpa only [hi, if_true, val_mul, r5_val, mate_val] using hc
    · simpa only [hi, if_false, mate_val] using hc
  rw [he]
  split_ifs
  · exact secondCenter.mul_mem r5_mem_secondCenter mate_mem_secondCenter
  · exact mate_mem_secondCenter

private theorem sylow_normalizes : S ≤ normalizer (secondCenter : Set Atlas1600Group) := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply (closure_le _).mpr
  intro g hg
  have hgs : g ∈ S := by rw [S, atlas1600SylowTwoSubgroup_eq]; exact subset_closure hg
  apply normalizes_of_generator_images g
  · have hc := congrArg Subtype.val (mem_center_iff.mp atlas1600R5_mem_center_sylowTwo ⟨g,hgs⟩)
    change g * atlas1600R5 = atlas1600R5 * g at hc
    rw [hc, mul_inv_cancel_right]
    exact r5_mem_secondCenter
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mate_image_mem 7 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])
    · exact mate_image_mem 6 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])
    · exact mate_image_mem 5 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])
    · exact mate_image_mem 4 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])
    · exact mate_image_mem 3 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])
    · exact mate_image_mem 2 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])
    · exact mate_image_mem 1 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])
    · exact mate_image_mem 0 _ (by simp only [atlas1600ParrottAssignment_val,
        Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator])

theorem second_le_normalizer_secondCenter : second ≤ normalizer (secondCenter : Set Atlas1600Group) :=
  sup_le sylow_normalizes ((closure_le _).mpr (by rintro g (rfl : g = r8); exact reflection_normalizes))

theorem r5_mem_second_core : atlas1600R5 ∈ second.pCoreIn 2 :=
  le_pCoreIn_of_normalizes secondCenter_isPGroup
    (secondCenter_le_sylow.trans sylow_le_second) second_le_normalizer_secondCenter r5_mem_secondCenter
end Tits.RelativeParabolicNormalizers

end
