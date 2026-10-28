module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.SmallOrbits
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.ImageSets
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Words
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.FirstImage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.PointwiseRigidity

/-!
# Four elementary normalizers lie in the unchanged ATLAS max4

Each of the four ambient normalizers preserves a common 28-point set: it is
an exact fixed-point set for elementary 1 and 2 and the union of the orbits
of size at most two for elementary 3 and 4. Both max4 generators preserve it.

To bound the full ambient set stabilizer, adjacency-profile fiber sizes
restrict the image of 0. Actual max4 word forests move that image back to 0.
Certified color refinement and a second word forest then fix 1; further
refinement fixes the remaining base points of the faithful action. Thus the
remaining element is the identity, identifying the full set stabilizer with
max4 and proving all four requested ambient normalizer bounds.

All finite identities and forest coverage are kernel-checked against the
preserved degree-4060 carrier and original ATLAS max4 words. No intrinsic
Sylow, elementary-catalogue, candidate cardinality, or ambient order premise
is used. Source: the ATLAS programs preserved in `SylowOvergroups/source/`,
GLS3 Table 5.3r, and the [Asc86b] application on Aschbacher--Smith printed p.511.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

namespace Max4Normalizers

open LocalCardinality.Max4

set_option maxRecDepth 30000 in
private theorem generator0_preserves : ∀ x : Fin 4060,
    GeneratorMaps.gen 0 x ∈ pointSet ↔ x ∈ pointSet := by
  apply Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem generator1_preserves : ∀ x : Fin 4060,
    GeneratorMaps.gen 1 x ∈ pointSet ↔ x ∈ pointSet := by
  apply Data.allFin
  decide +kernel

/-- Both unchanged ATLAS max4 generators preserve the common set. -/
public theorem max4_le_pointSetStabilizer : max4 ≤ pointSetStabilizer := by
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl | hg)
  · apply (mem_pointSetStabilizer _).mpr
    intro x
    change modelSubgroup.subtype max4Generators.1 x ∈ pointSet ↔ x ∈ pointSet
    rw [← generator0_eq, ← GeneratorMaps.gen_eq]
    exact generator0_preserves x
  · obtain rfl := Set.mem_singleton_iff.mp hg
    apply (mem_pointSetStabilizer _).mpr
    intro x
    change modelSubgroup.subtype max4Generators.2 x ∈ pointSet ↔ x ∈ pointSet
    rw [← generator1_eq, ← GeneratorMaps.gen_eq]
    exact generator1_preserves x

/-- Two independent word and rigidity certificates identify the whole
ambient set stabilizer with the unchanged ATLAS candidate. -/
public theorem pointSetStabilizer_le_max4_of_certificates
    (hwords : WordReachability) (hrigid : ImageRigidity) :
    pointSetStabilizer ≤ max4 := by
  intro p hp
  obtain ⟨g, hg, hg0⟩ := hwords.1 _ (hrigid.1 p hp)
  let q : Model := g⁻¹ * p
  have hq : q ∈ pointSetStabilizer := pointSetStabilizer.mul_mem
    (pointSetStabilizer.inv_mem (max4_le_pointSetStabilizer hg)) hp
  have hq0 : q • (0 : Fin 4060) = 0 := by
    change g⁻¹ • (p • (0 : Fin 4060)) = 0
    rw [← hg0, inv_smul_smul]
  obtain ⟨h, hh, hh0, hh1⟩ := hwords.2 _ (hrigid.2.1 q hq hq0)
  have hr : h⁻¹ * q ∈ pointSetStabilizer := pointSetStabilizer.mul_mem
    (pointSetStabilizer.inv_mem (max4_le_pointSetStabilizer hh)) hq
  have hr0 : (h⁻¹ * q) • (0 : Fin 4060) = 0 := by
    rw [mul_smul, hq0]
    exact inv_smul_eq_iff.mpr hh0.symm
  have hr1 : (h⁻¹ * q) • (1 : Fin 4060) = 1 := by
    rw [mul_smul, ← hh1, inv_smul_smul]
  have he : h⁻¹ * q = 1 := hrigid.2.2 _ hr hr0 hr1
  have hqmem : q ∈ max4 := (inv_mul_eq_one.mp he) ▸ hh
  have hp' := max4.mul_mem hg hqmem
  simpa only [q, mul_inv_cancel_left] using hp'

/-- Kernel-certified image bounds and pointwise rigidity for the full set stabilizer. -/
public theorem imageRigidity : ImageRigidity :=
  ⟨first_image, RefinementCertificate.second_image, RefinementCertificate.fix_two_eq_one⟩

/-- The full set stabilizer in the actual Rudvalis carrier is exactly max4. -/
public theorem pointSetStabilizer_eq_max4 : pointSetStabilizer = max4 :=
  le_antisymm (pointSetStabilizer_le_max4_of_certificates wordReachability imageRigidity)
    max4_le_pointSetStabilizer

end Max4Normalizers

/-- Conditional final assembly. Both finite geometric certificates must be
proved before this gives the requested unconditional normalizer bounds. -/
public theorem max4NormalizerBounds_of_geometry
    (hwords : Max4Normalizers.WordReachability)
    (hrigid : Max4Normalizers.ImageRigidity) : Max4NormalizerBounds := by
  intro i hi0 hi5
  exact (Max4Normalizers.normalizer_le_pointSetStabilizer i hi0 hi5).trans
    (Max4Normalizers.pointSetStabilizer_le_max4_of_certificates hwords hrigid)

/-- All four fixed elementary normalizers are contained in the original max4. -/
public theorem max4NormalizerBounds : Max4NormalizerBounds :=
  max4NormalizerBounds_of_geometry Max4Normalizers.wordReachability Max4Normalizers.imageRigidity

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
