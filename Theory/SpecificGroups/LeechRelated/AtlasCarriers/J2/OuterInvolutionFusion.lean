module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionFusion.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Placement
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Exhaustive fusion of outer involutions in the Hall--Janko extension

Every involution is conjugate into the checked Sylow subgroup of order 256.
Its intersection with the original carrier is the inner Sylow subgroup;
thus an outer involution lies in the other coset, enumerated by 128 words.
The checked conjugators fuse all involutions in that coset to the displayed
normalizing involution. This is exhaustive fusion in the actual permutation
extension, independent of any identification with the full automorphism group.

Source: GLS3, Table 5.3g, class 2C; Aschbacher--Smith 16.1.5(8), p.1172.
The residual-three-core calculation is a separate consequence, not asserted here.
-/

public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionFusion
open ExceptionalParabolics ExceptionalParabolics.Seed
open ExceptionalParabolics.SecondParabolic ExceptionalParabolics.PairNormalizer
open scoped Pointwise

private instance inner_normal : intoExtension.range.Normal where
  conj_mem := by
    rintro x ⟨g, rfl⟩ y
    refine ⟨extensionAction y g, ?_⟩
    apply extensionAction_injective
    simp only [extensionAction_inner, map_mul, map_inv]
    ext z
    simp

/-- Elements of the outer Sylow lying outside the carrier have the enumerated
outer-coset form, without an involution assumption. -/
theorem outerSylow_coset_cover {x : Extension} (hx : x ∈ outerS)
    (ho : x ∉ intoExtension.range) :
    ∃ i : Fin 128, x = intoExtension (sElement i) * outerElement := by
  have hp : x ∈ (s.map intoExtension : Set Extension) *
      (Subgroup.zpowers outerElement : Set Extension) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (Subgroup.zpowers_le.mpr outerElement_normalizes_s)]
    exact hx
  obtain ⟨y, ⟨z, hz, rfl⟩, t, ht, hyt⟩ := hp
  have htne : outerElement ≠ 1 := fun h =>
    outerElement_not_mem_range (h ▸ intoExtension.range.one_mem)
  have htorder : orderOf outerElement = 2 := orderOf_eq_prime outerElement_sq htne
  classical
  change t ∈ Subgroup.zpowers outerElement at ht
  rw [(isOfFinOrder_of_finite outerElement).mem_zpowers_iff_mem_range_orderOf,
    htorder] at ht
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
  have hj' : j = 0 ∨ j = 1 := by have := Finset.mem_range.mp hj; omega
  rcases hj' with rfl | rfl
  · have he : intoExtension z = x := by simpa using hyt
    exact (ho (he ▸ ⟨z, rfl⟩)).elim
  · obtain ⟨i, rfl⟩ := exists_sElement hz
    exact ⟨i, by simpa using hyt.symm⟩

/-- Every outer involution of the actual permutation extension belongs to
its unique outer involution class. -/
theorem extension_outer_involution_fusion (x : Extension) (hx : orderOf x = 2)
    (ho : x ∉ intoExtension.range) : IsConj extensionInvolution x := by
  obtain ⟨z, hz⟩ := (outerSylow FirstParabolic.card_l₁).exists_isConj_of_orderOf_eq_prime_pow
    (hx.trans (pow_one 2).symm)
  have hzout : (z : Extension) ∉ intoExtension.range := by
    intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp hz.symm
    exact ho (hg ▸ (inferInstance : intoExtension.range.Normal).conj_mem _ h g)
  obtain ⟨i, hi⟩ := outerSylow_coset_cover z.property hzout
  have hsq : (intoExtension (sElement i) * outerElement) ^ 2 = 1 := by
    rw [← hi]
    have hpow : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    exact isConj_one_right.mp (hpow ▸ hz.pow 2)
  exact ((sylow_coset_fusion i hsq).trans (by rw [hi])).trans hz.symm

end Sporadic.LeechRelated.J2.OuterInvolutionFusion
