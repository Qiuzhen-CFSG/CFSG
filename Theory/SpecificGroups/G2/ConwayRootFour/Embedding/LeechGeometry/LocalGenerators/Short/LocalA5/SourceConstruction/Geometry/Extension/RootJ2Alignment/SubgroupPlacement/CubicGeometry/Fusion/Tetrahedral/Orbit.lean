module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Orbit.Preparation

/-!
# Assembling the reference tetrahedral orbit from involution incidence

Move the transported double transposition back by an element of the fixed
cubic centralizer. The transported tetrahedron then contains the marked
involution. Its incidence orbit supplies a second conjugator in the same
centralizer; their product is the required tetrahedral conjugator.

This is conditional assembly. Both geometric inputs still require proofs on
the literal Leech quotient, including any source root-class identifications.
It does not assert `referenceTetrahedralOrbit` without those proofs, and uses
neither ambient cubic fusion nor a normalizer-action realization.

Source: Aschbacher, *Sporadic Groups* (1994), the root conventions after
48.3 (pp.268–269) and 49.1–49.5 (pp.280–284).
-/

@[expose] public noncomputable section
open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

private theorem orbit_map_conj_mul (g h : LeechCentralQuotient)
    (J : Subgroup LeechCentralQuotient) :
    J.map (MulAut.conj (g * h)).toMonoidHom =
      (J.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The two geometric orbit statements give the exact published reference
contract, with the actor still in its pointwise cubic centralizer. -/
theorem referenceTetrahedralOrbit_of_involution_incidence
    (hinvolution : ReferenceInvolutionOrbit)
    (hincidence : ReferenceTetrahedralIncidence) : ReferenceTetrahedralOrbit := by
  intro g hg
  have hgu : MulAut.conj g orbitInvolution ∈ referenceCubicCentralizer := by
    rw [mem_referenceCubicCentralizer_iff]
    exact hg (Subgroup.mem_zpowers _) _ ⟨orbitInvolution, orbitInvolution_mem_I, rfl⟩
  obtain ⟨c, hc, hcu⟩ := hinvolution g hgu
  have hcg : Subgroup.zpowers RootModel.referenceCubic ≤ Subgroup.centralizer
      (I.map (MulAut.conj (c * g)).toMonoidHom : Set LeechCentralQuotient) := by
    rw [orbit_map_conj_mul]
    rintro p hp _ ⟨z, hz, rfl⟩
    have hcp : MulAut.conj c p = p := by
      change c * p * c⁻¹ = p
      rw [← hc p hp, mul_inv_cancel_right]
    change MulAut.conj c z * p = p * MulAut.conj c z
    have he := congrArg (MulAut.conj c) (hg hp z hz)
    simpa only [map_mul, hcp] using he
  have hufix : MulAut.conj (c * g) orbitInvolution = orbitInvolution := by
    simpa only [MulAut.conj_apply, mul_inv_rev, mul_assoc] using hcu
  obtain ⟨d, hd, _, hdI⟩ := hincidence (c * g) hcg hufix
  refine ⟨d * c, referenceCubicCentralizer.mul_mem hd hc, ?_⟩
  rw [orbit_map_conj_mul, ← orbit_map_conj_mul c g]
  exact hdI

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
