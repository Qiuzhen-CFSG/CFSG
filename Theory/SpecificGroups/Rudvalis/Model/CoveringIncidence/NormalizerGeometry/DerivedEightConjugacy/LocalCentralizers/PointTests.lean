module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Data
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.PcComparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers

/-!
# Two-point certificates for the local Rudvalis calculation

The previously checked rigidity of the max4 point-set stabilizer says that
an element fixing points 0 and 1 is the identity. Since `localP` lies in
max4, two point images suffice to certify equalities between local words.
This avoids introducing permutation tables or checking every word identity
on all 4060 points. The three representative involutions are an application.

All comparisons use the original carrier and its checked coordinate maps.
Source attribution for those maps is in `ElementaryCatalogue.PcComparison`;
the rigidity input is `Max4Normalizers.PointwiseRigidity`. The application
is the local criterion motivated by GLS3 Table 5.3r and pp.291–292.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate

/-- Equal images at the certified base pair determine an element of `localP`. -/
public theorem eq_of_two_points {x y : Model} (hx : x ∈ localP) (hy : y ∈ localP)
    (h0 : modelSubgroup.subtype x 0 = modelSubgroup.subtype y 0)
    (h1 : modelSubgroup.subtype x 1 = modelSubgroup.subtype y 1) : x = y := by
  apply Eq.symm
  apply inv_mul_eq_one.mp
  apply Max4Normalizers.RefinementCertificate.fix_two_eq_one (y⁻¹ * x)
  · exact Max4Normalizers.max4_le_pointSetStabilizer
      (localP_le_max4 (localP.mul_mem (localP.inv_mem hy) hx))
  · change modelSubgroup.subtype y⁻¹ (modelSubgroup.subtype x 0) = 0
    rw [h0]
    exact inv_smul_smul y (0 : Fin 4060)
  · change modelSubgroup.subtype y⁻¹ (modelSubgroup.subtype x 1) = 1
    rw [h1]
    exact inv_smul_smul y (1 : Fin 4060)

/-- Square-one testing on two points, with local membership retained. -/
public theorem square_eq_one_of_two_points {x : Model} (hx : x ∈ localP)
    (h0 : modelSubgroup.subtype x (modelSubgroup.subtype x 0) = 0)
    (h1 : modelSubgroup.subtype x (modelSubgroup.subtype x 1) = 1) : x ^ 2 = 1 := by
  apply eq_of_two_points (localP.pow_mem hx 2) localP.one_mem
  · rw [pow_two]
    exact h0
  · rw [pow_two]
    exact h1

/-- Commutation testing on two points, with both local memberships retained. -/
public theorem commute_of_two_points {x y : Model} (hx : x ∈ localP) (hy : y ∈ localP)
    (h0 : modelSubgroup.subtype x (modelSubgroup.subtype y 0) =
      modelSubgroup.subtype y (modelSubgroup.subtype x 0))
    (h1 : modelSubgroup.subtype x (modelSubgroup.subtype y 1) =
      modelSubgroup.subtype y (modelSubgroup.subtype x 1)) : Commute x y :=
  eq_of_two_points (localP.mul_mem hx hy) (localP.mul_mem hy hx) h0 h1

private theorem representative_square_points : ∀ r : Fin 3,
    normalFormPermutation (representativeIndex r)
      (normalFormPermutation (representativeIndex r) 0) = 0 ∧
    normalFormPermutation (representativeIndex r)
      (normalFormPermutation (representativeIndex r) 1) = 1 := by
  decide +kernel

/-- The chosen words are square-one elements of the actual model. -/
public theorem representative_square (r : Fin 3) : representative r ^ 2 = 1 := by
  apply square_eq_one_of_two_points (representative_mem r)
  · simpa only [representative, ← normalFormPermutation_eq] using
      (representative_square_points r).1
  · simpa only [representative, ← normalFormPermutation_eq] using
      (representative_square_points r).2

end Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
