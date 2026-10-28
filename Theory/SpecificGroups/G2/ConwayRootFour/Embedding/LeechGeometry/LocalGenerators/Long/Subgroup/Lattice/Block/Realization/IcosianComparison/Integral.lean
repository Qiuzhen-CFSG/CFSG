module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.IcosianComparison.Core
public import Theory.AtlasPort.Janko2.Lattices.IcosianIntegralComparison

/-!
# Both integral containments for the quaternion comparison

The forward coefficient table writes each image basis vector as an integral
combination of the existing 36 icosian generators. The reverse table writes
every one of those generators in the image basis. The proved generation
criterion extends this to the actual congruence lattice, giving both directions
of membership without lattice recognition or any additional assumption.

Source generator membership, generation, and images are the attributed ports
of Gerald Höhn, ATLAS revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Codes
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
namespace IcosianComparison

private theorem basisImages_forward : basisImages = sourceImages * forwardCoefficients :=
  integer_certificates.2.2.2.2.2.1
private theorem basisImages_reverse : basisImages * reverseCoefficients = sourceImages :=
  integer_certificates.2.2.2.2.2.2

private noncomputable def sourceGenerator (j : Fin 36) : IcosianRationalCoordinates :=
  icosianCoordinateEmbedding (icosianComparisonSourceGenerator j)

private theorem sourceGenerator_mem (j : Fin 36) : sourceGenerator j ∈ rationalIcosianLattice :=
  Submodule.mem_map.mpr ⟨_, icosianComparisonSourceGenerator_mem j, rfl⟩

private theorem sourceGenerator_image (j : Fin 36) :
    icosianComparison (sourceGenerator j) = fun p => (sourceImages p j : ℚ) :=
  (icosianComparison_forward_arithmetic j).1

private theorem sourceImages_mulVec (z : Fin 36 → ℤ) :
    sourceImages.map (Int.castRingHom ℚ) *ᵥ (fun j => (z j : ℚ)) =
      icosianComparison (∑ j, z j • sourceGenerator j) := by
  simp only [map_sum, map_zsmul, sourceGenerator_image]
  ext p
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

private theorem cast_mulVec {m n : Type*} [Fintype n] (M : Matrix m n ℤ) (z : n → ℤ) :
    (fun i => ((M *ᵥ z) i : ℚ)) =
      M.map (Int.castRingHom ℚ) *ᵥ (fun i => (z i : ℚ)) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

private theorem compared_basis (z : Index → ℤ) :
    icosianComparison (quaternionComparison (basisMap z)) =
      basisImages.map (Int.castRingHom ℚ) *ᵥ integerEmbedding z := by
  rw [icosianComparison_apply, quaternionComparison_coordinates, basisMap_apply,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, candidate_basis]

private theorem forward (x : Space) (hx : x ∈ lattice) : quaternionComparison x ∈ rationalIcosianLattice := by
  obtain ⟨z,rfl⟩ := hx
  have h : quaternionComparison (basisMap z) = ∑ j, (forwardCoefficients *ᵥ z) j • sourceGenerator j := by
    apply icosianComparison.injective
    rw [compared_basis, basisImages_forward, Matrix.map_mul, ← Matrix.mulVec_mulVec]
    change sourceImages.map (Int.castRingHom ℚ) *ᵥ
      (forwardCoefficients.map (Int.castRingHom ℚ) *ᵥ (fun i => (z i : ℚ))) = _
    rw [← cast_mulVec, sourceImages_mulVec]
  rw [h]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (sourceGenerator_mem j)

private theorem sourceGenerator_preimage (j : Fin 36) :
    quaternionComparison (basisMap (fun i => reverseCoefficients i j)) = sourceGenerator j := by
  apply icosianComparison.injective
  rw [compared_basis, sourceGenerator_image]
  ext p
  have hi := congrArg (fun M : Matrix Omega (Fin 36) ℤ => M p j) basisImages_reverse
  change (∑ i, (basisImages p i : ℚ) * (reverseCoefficients i j : ℚ)) = _
  change (∑ i, basisImages p i * reverseCoefficients i j) = sourceImages p j at hi
  exact_mod_cast hi

private theorem reverse (z : IcosianRationalCoordinates) (hz : z ∈ rationalIcosianLattice) :
    quaternionComparison.symm z ∈ lattice := by
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hz
  let S : Submodule ℤ IcosianCoordinates := lattice.comap
    ((quaternionComparison.symm.toLinearMap.restrictScalars ℤ).comp icosianCoordinateEmbedding)
  have hS (j : Fin 36) : icosianComparisonSourceGenerator j ∈ S := by
    change quaternionComparison.symm (sourceGenerator j) ∈ lattice
    rw [← sourceGenerator_preimage j, LinearEquiv.symm_apply_apply]
    exact ⟨_,rfl⟩
  exact icosianLeechModule_le_of_generators S hS hv

end IcosianComparison

/-- Both membership directions for the literal integral lattices. -/
theorem quaternionComparison_lattice (x : Space) :
    x ∈ lattice ↔ quaternionComparison x ∈ rationalIcosianLattice := by
  constructor
  · exact IcosianComparison.forward x
  · intro hx
    simpa only [LinearEquiv.symm_apply_apply] using
      IcosianComparison.reverse (quaternionComparison x) hx

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
