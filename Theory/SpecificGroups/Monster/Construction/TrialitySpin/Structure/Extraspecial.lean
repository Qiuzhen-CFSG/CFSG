module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Quotients
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticSpace
public import Theory.ElementaryAbelian.ExtraspecialEquiv
/-!
# Extraspeciality after quotienting by the triality involution

The word-square law puts every square of the image of `Q1` in its center.
The preceding quotient calculation gives center order two and central quotient
order `2^24`. A group of exponent two is abelian, so these facts prove
extraspeciality, and the canonical isomorphism transports it to `Q1/⟨k1⟩`.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.4(2), pp. 61–62.
The plus-type identification is supplied by the quadratic quotient module.
-/

public section
open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

theorem Q1Image_square_mem_center (x : Q1Image) : x ^ 2 ∈ Subgroup.center Q1Image := by
  obtain ⟨q,rfl⟩ := q1ImageMap_surjective x
  obtain ⟨⟨d,t,c⟩,rfl⟩ := q1Param_bijective.surjective q
  have h : (q1ImageMap (q1Param (d,t,c))) ^ 2 =
      q1ImageCenterGenerator ^ (coordinateQuadratic (q1WordCoordinates d t c)).val := by
    apply Subtype.ext
    change nQuotientMap (q1Word d t c).val ^ 2 = nQuotientMap z1N ^ _
    rw [← map_pow,q1Word_sq,map_pow]
  rw [h,Q1Image_center]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem Q1Image_central_quotient_elementary :
    IsElementaryAbelian 2 (Q1Image ⧸ Subgroup.center Q1Image) := by
  have hs (x : Q1Image ⧸ Subgroup.center Q1Image) : x ^ 2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q1Image) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Q1Image_square_mem_center x)
  have hi (x : Q1Image ⧸ Subgroup.center Q1Image) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hs x
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev,hi,hi]

theorem Q1Image_central_quotient_card :
    Nat.card (Q1Image ⧸ Subgroup.center Q1Image) = 2 ^ 24 := by
  have h := (Subgroup.center Q1Image).card_eq_card_quotient_mul_card_subgroup
  rw [Q1Image_card,Q1Image_center_card] at h
  omega

theorem Q1Image_extraspecial : IsExtraspecial 2 Q1Image where
  center_order_p := Q1Image_center_card
  quotient_elementary_abelian := Q1Image_central_quotient_elementary
  quotient_nontrivial := by
    let := Fintype.ofFinite (Q1Image ⧸ Subgroup.center Q1Image)
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card,Q1Image_central_quotient_card]
    decide

theorem Q1Quotient_extraspecial : IsExtraspecial 2 Q1Quotient :=
  IsExtraspecial.of_mulEquiv q1QuotientEquivImage.symm Q1Image_extraspecial
end Sporadic.Monster.Construction.TrialitySpin
