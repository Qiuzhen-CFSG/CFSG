module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.Displacement
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Certificate
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder

/-!
# Relative centralizers of the Tits reflection overlaps

For the first reflection, the overlap contains `s2`; for the second, it
contains `s7`, by Parrott relations VII and VIII. Write an element of either
parabolic as a Sylow word followed by a rotation power.
Commutation with the chosen overlap element, even just at point zero,
forces that power to be zero. Thus both relative centralizers lie in S.

These are unconditional bounds for the actual Atlas1600 Parrott marking,
used by `kernel_isPGroup_of_overlap_centralizers`. They require no
identification or exhaustiveness assumption on the automorphism group.
Source: Parrott (1972), p.683; Aschbacher–Smith, printed p.510; compare
GLS3, 2.5.15. Generator and conjugation conventions are recorded in
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

@[expose] public section
namespace Tits.OuterOddSubgroups
open Subgroup ExceptionalParabolics OverlapCentralizers

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_pow (x : Atlas1600Group) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl

private theorem s_mem (i : ParrottGenerator) (h1 : i ≠ .r1) (h8 : i ≠ .r8) :
    atlas1600ParrottAssignment i ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply subset_closure
  cases i <;> simp_all

private theorem first_witness_mem :
    atlas1600ParrottAssignment .s2 ∈
      reflectionOverlap (atlas1600ParrottAssignment .r1) := by
  refine ⟨s_mem _ (by decide) (by decide), ?_⟩
  have hr : atlas1600ParrottAssignment .r1 * atlas1600ParrottAssignment .r1 = 1 := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of, pow_two]
      using atlas1600ParrottAssignment_relations .i_r1
  have he : atlas1600ParrottAssignment .r1 * atlas1600ParrottAssignment .s2 *
      atlas1600ParrottAssignment .r1 = atlas1600ParrottAssignment .s8 := by
    apply mul_inv_eq_one.mp
    simpa only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
      using atlas1600ParrottAssignment_relations .vii_s2
  change atlas1600ParrottAssignment .r1 * atlas1600ParrottAssignment .s2 *
    (atlas1600ParrottAssignment .r1)⁻¹ ∈ S
  rw [inv_eq_of_mul_eq_one_right hr, he]
  exact s_mem _ (by decide) (by decide)

private theorem second_witness_mem :
    atlas1600ParrottAssignment .s7 ∈
      reflectionOverlap (atlas1600ParrottAssignment .r8) := by
  refine ⟨s_mem _ (by decide) (by decide), ?_⟩
  have hr : atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .r8 = 1 := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of, pow_two]
      using atlas1600ParrottAssignment_relations .i_r8
  have he : atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .s7 *
      atlas1600ParrottAssignment .r8 = (atlas1600ParrottAssignment .s7)⁻¹ := by
    apply mul_inv_eq_one.mp
    simpa only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
      using atlas1600ParrottAssignment_relations .viii_s7
  change atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .s7 *
    (atlas1600ParrottAssignment .r8)⁻¹ ∈ S
  rw [inv_eq_of_mul_eq_one_right hr, he]
  exact S.inv_mem (s_mem _ (by decide) (by decide))

private theorem centralizer_point {r x : Atlas1600Group}
    (hx : x ∈ centralizer (reflectionOverlap r : Set Atlas1600Group))
    (i : ParrottGenerator) (hi : atlas1600ParrottAssignment i ∈ reflectionOverlap r) :
    Certificate.testPair x.val (Atlas1600ParrottData.permutation i) = true := by
  have h := congrArg (fun y : Atlas1600Group => y.val 0)
    ((mem_centralizer_iff.mp hx) _ hi)
  simp only [val_mul, atlas1600ParrottAssignment_val, Equiv.Perm.mul_apply] at h
  exact beq_iff_eq.mpr h.symm

private theorem first_test {x : Atlas1600Group}
    (hx : x ∈ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r1) : Set Atlas1600Group)) :
    Certificate.testFirst x.val = true :=
  centralizer_point hx .s2 first_witness_mem

private theorem second_test {x : Atlas1600Group}
    (hx : x ∈ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r8) : Set Atlas1600Group)) :
    Certificate.testSecond x.val = true :=
  centralizer_point hx .s7 second_witness_mem

/-- The relative centralizer of the first reflection overlap lies in the Sylow subgroup. -/
theorem first_overlap_centralizer_le :
    first ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r1) : Set Atlas1600Group) ≤ S := by
  rintro x ⟨hx, hc⟩
  obtain ⟨⟨n, j⟩, he⟩ := firstNormalForm_surjective ⟨x, hx⟩
  have hv := congrArg Subtype.val he
  simp only [firstNormalForm_val] at hv
  have ht := first_test hc
  rw [← hv] at ht
  simp only [val_mul, val_pow, firstRotation, atlas1600SylowTwoNormalForm_val,
    atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation] at ht
  change Certificate.testFirst (Atlas1600SylowTwoCertificate.normalForm n *
    (Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm) ^ j.val) = true at ht
  have hj := Certificate.first_coset_zero n j ht
  subst j
  rw [← hv]
  simpa only [Fin.val_zero, pow_zero, mul_one] using atlas1600SylowTwoNormalForm_mem n

/-- The relative centralizer of the second reflection overlap lies in the Sylow subgroup. -/
theorem second_overlap_centralizer_le :
    second ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r8) : Set Atlas1600Group) ≤ S := by
  rintro x ⟨hx, hc⟩
  obtain ⟨⟨n, j⟩, he⟩ := RelativeSecondBlockLayers.secondNormalForm_surjective ⟨x, hx⟩
  have hv := congrArg Subtype.val he
  simp only [RelativeSecondBlockLayers.secondNormalForm_val] at hv
  have ht := second_test hc
  rw [← hv] at ht
  simp only [RelativeSecondBlockLayers.SecondOrder.rep, val_mul, val_pow,
    atlas1600SylowTwoNormalForm_val, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation] at ht
  change Certificate.testSecond (Atlas1600SylowTwoCertificate.normalForm n *
    (Atlas1600ParrottData.s8Perm * Atlas1600ParrottData.r8Perm) ^ j.val) = true at ht
  have hj := Certificate.second_coset_zero n j ht
  subst j
  rw [← hv]
  simpa only [RelativeSecondBlockLayers.SecondOrder.rep, Fin.val_zero, pow_zero, mul_one]
    using atlas1600SylowTwoNormalForm_mem n

end Tits.OuterOddSubgroups
end
