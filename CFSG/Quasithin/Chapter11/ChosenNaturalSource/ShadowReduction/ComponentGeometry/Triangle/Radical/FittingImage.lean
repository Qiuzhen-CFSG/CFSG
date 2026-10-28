module

public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity
public import Theory.GroupTheory.Fitting.PrimeSubgroups
public import Theory.GroupAction.SmallQuotientCentralization
public import Theory.GroupTheory.Commutator.SmallNormalizedImage

/-!
# Two-subgroup images in the surviving radical argument

Every two-subgroup of O₂,F(J) lies in O₂(J), since the Fitting subgroup
of J/O₂(J) has odd order. Thus an index at most two for O₂,F(J) in
O∞(J) bounds the image of any two-subgroup of the radical in J/O₂(J).
Every normalizing actor fixes an image of order at most two.

This proves the deduction from the index bound, not the model-specific
index bound or radical containment. Both remain independent obligations
in the strict-component cases of the original source.
Source: Aschbacher--Smith, 11.4.1(3), printed p.776.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {J : Type*} [Group J] [Finite J]

/-- Two-subgroups meet the Fitting preimage only in the original two-core. -/
theorem two_intersection_fitting_le_core (A : Subgroup J) (hA : IsPGroup 2 A) :
    A ⊓ twoFittingCore J ≤ pCore 2 J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hF : (A ⊓ twoFittingCore J).map q ≤ fittingSubgroup (J ⧸ pCore 2 J) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha.2
  have hc := IsPGroup.le_pCore_of_le_fitting ((hA.to_le inf_le_left).map q) hF
  rw [pCore_quotient_pCore_eq_bot 2] at hc
  intro a ha
  exact (QuotientGroup.eq_one_iff a).mp (mem_bot.mp (hc (mem_map_of_mem q ha)))

/-- The source Fitting index controls the full two-subgroup, not only its
elementary abelian subgroups. -/
theorem two_subgroup_core_index_le_two (A : Subgroup J) (hA : IsPGroup 2 A)
    (hAR : A ≤ solvableRadical J)
    (hi : (twoFittingCore J).relIndex (solvableRadical J) ≤ 2) :
    (pCore 2 J).relIndex A ≤ 2 := by
  have hsmall : (twoFittingCore J).relIndex A ≤ 2 :=
    (relIndex_le_of_le_right (H := twoFittingCore J) hAR
      (show ((twoFittingCore J).subgroupOf (solvableRadical J)).index ≠ 0 from
        index_ne_zero_of_finite)).trans hi
  have hle : A ⊓ twoFittingCore J ≤ A ⊓ pCore 2 J :=
    le_inf inf_le_left (two_intersection_fitting_le_core A hA)
  have hh := relIndex_le_of_le_left (L := A) hle
    (show ((A ⊓ twoFittingCore J).subgroupOf A).index ≠ 0 from index_ne_zero_of_finite)
  rw [inf_relIndex_left, inf_relIndex_left] at hh
  exact hh.trans hsmall

/-- Any actual homomorphism killing O₂(J) has image of order at most two
on the original two-subgroup of the radical. -/
theorem two_subgroup_image_card_le_two {B : Type*} [Group B]
    (φ : J →* B) (hφ : pCore 2 J ≤ φ.ker)
    (A : Subgroup J) (hA : IsPGroup 2 A) (hAR : A ≤ solvableRadical J)
    (hi : (twoFittingCore J).relIndex (solvableRadical J) ≤ 2) :
    Nat.card (A.map φ) ≤ 2 := by
  rw [← relIndex_ker]
  exact (relIndex_le_of_le_left (L := A) hφ
    (show ((pCore 2 J).subgroupOf A).index ≠ 0 from index_ne_zero_of_finite)).trans
    (two_subgroup_core_index_le_two A hA hAR hi)

/-- Internal normalizers fix the resulting quotient image pointwise. -/
theorem commutator_le_core_of_fitting_index (A X : Subgroup J)
    (hA : IsPGroup 2 A) (hAR : A ≤ solvableRadical J)
    (hi : (twoFittingCore J).relIndex (solvableRadical J) ≤ 2)
    (hn : X ≤ normalizer (A : Set J)) : ⁅A, X⁆ ≤ pCore 2 J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : pCore 2 J ≤ q.ker := by rw [QuotientGroup.ker_mk']
  have hh := commutator_le_ker_of_normalized_image_card_le_two q X A hn
    (two_subgroup_image_card_le_two q hq A hA hAR hi)
  simpa only [q, QuotientGroup.ker_mk', commutator_comm X A] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
