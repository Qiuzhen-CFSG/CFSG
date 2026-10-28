module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.IntegralAlignment.WordChecks

/-!
# An integral word aligning the Eisenstein and reference cubics

Let X and Y be the retained integral icosian generators, and A and B the two
integral block generators. The word Y X B Y A B A Y is an actual Leech isometry.
The checked rational matrices show that it intertwines the scalar Eisenstein
cube root with the exact commutator-fourth-power reference lift. Each factor
commutes with the integral rational scalars, so their projective image is fixed.

This supplies the cubic part of the simultaneous comparison needed for
Aschbacher, *Sporadic Groups* (1994), 49.2 and 49.5. The inherited constructions
of every factor preserve the form and both integral lattice containments.
The matrix data retain John Bray's and Gerald Höhn's ATLAS attribution and
license as documented in WordData and LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
open Long.Block Long.Block.Realization
open Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Sporadic.LeechRelated.J2.IcosianComparison.Generators.RelatorMatrices
namespace IntegralAlignment
open WordData

private def half (N : Matrix Index Index ℤ) : RealMatrix :=
  (1/2 : ℚ) • N.map (Int.castRingHom ℚ)

private theorem half_mul (A B C : Matrix Index Index ℤ)
    (h : A * B = (2 : ℤ) • C) : half A * half B = half C := by
  have hh := congrArg (fun M => M.map (Int.castRingHom ℚ)) h
  simp only [two_smul, Matrix.map_add _ (map_add (Int.castRingHom ℚ)), Matrix.map_mul] at hh
  unfold half
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hh]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply]
  ring

private theorem comparison_matrix (N : Matrix Index Index ℤ)
    (M : Matrix IcosianRealIndex IcosianRealIndex ℤ)
    (h : (2 : ℤ) • (Long.Block.Realization.IcosianComparison.numerator * N) =
      M * Long.Block.Realization.IcosianComparison.numerator) :
    comparisonCandidateMatrix * half N =
      ((1/4 : ℚ) • M.map (Int.castRingHom ℚ)) * comparisonCandidateMatrix := by
  have hh := congrArg (fun M => M.map (Int.castRingHom ℚ)) h
  simp only [two_smul, Matrix.map_add _ (map_add (Int.castRingHom ℚ)), Matrix.map_mul] at hh
  rw [Long.Block.Realization.IcosianComparison.specifications.1]
  unfold half
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, ← hh]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply]
  ring

private theorem hermitian_on_comparison (g : icosianHermitianGroup)
    (N : Matrix Index Index ℤ)
    (h : comparisonCandidateMatrix * half N =
      hermitianRealMatrix (matrixHom g) * comparisonCandidateMatrix) (x : Space) :
    (fullIsometryEquiv (icosianHermitianToCo0 g)).val (matrixComparison x) =
      matrixComparison (half N *ᵥ x) := by
  rw [icosianHermitianToCo0_extension]
  change icosianComparison (g.val (icosianComparison.symm
    (icosianComparison (quaternionComparison x)))) =
    icosianComparison (quaternionComparison (half N *ᵥ x))
  rw [icosianComparison.symm_apply_apply]
  apply congrArg icosianComparison
  apply icosianRealCoordinates.injective
  rw [hermitianRealMatrix_apply, quaternionComparison_coordinates,
    quaternionComparison_coordinates, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

private def xIsometry : LeechIsometryGroup := icosianHermitianToCo0 xLift
private def yIsometry : LeechIsometryGroup := icosianHermitianToCo0 yLift
private def aIsometry : LeechIsometryGroup :=
  matrixToLeech ⟨generatorA, Subgroup.subset_closure (by simp)⟩
private def bIsometry : LeechIsometryGroup :=
  matrixToLeech ⟨generatorB, Subgroup.subset_closure (by simp)⟩

private theorem x_apply (x : Space) :
    (fullIsometryEquiv xIsometry).val (matrixComparison x) =
      matrixComparison (half xNumerator *ᵥ x) := by
  apply hermitian_on_comparison
  rw [matrixHom_xLift, hermitian_specifications.1]
  exact comparison_matrix _ _ comparison_certificates.1

private theorem y_apply (x : Space) :
    (fullIsometryEquiv yIsometry).val (matrixComparison x) =
      matrixComparison (half yNumerator *ᵥ x) := by
  apply hermitian_on_comparison
  rw [matrixHom_yLift, hermitian_specifications.2.1]
  exact comparison_matrix _ _ comparison_certificates.2.1

private theorem reference_apply (x : Space) :
    (fullIsometryEquiv (icosianHermitianToCo0 referenceLift)).val (matrixComparison x) =
      matrixComparison (half referenceNumerator *ᵥ x) := by
  apply hermitian_on_comparison
  rw [referenceLift_matrix, hermitian_specifications.2.2]
  exact comparison_matrix _ _ comparison_certificates.2.2

private theorem a_apply (x : Space) :
    (fullIsometryEquiv aIsometry).val (matrixComparison x) =
      matrixComparison (half aNumerator *ᵥ x) := by
  rw [aIsometry, matrixToLeech_generatorA, block_specifications.1]
  rfl

private theorem b_apply (x : Space) :
    (fullIsometryEquiv bIsometry).val (matrixComparison x) =
      matrixComparison (half bNumerator *ᵥ x) := by
  rw [bIsometry, matrixToLeech_generatorB, block_specifications.2.1]
  rfl

/-- An eight-factor word in already constructed integral Leech isometries. -/
def cubicWord : LeechIsometryGroup :=
  icosianHermitianToCo0 yLift * icosianHermitianToCo0 xLift *
    matrixToLeech ⟨generatorB, Subgroup.subset_closure (by simp)⟩ *
    icosianHermitianToCo0 yLift *
    matrixToLeech ⟨generatorA, Subgroup.subset_closure (by simp)⟩ *
    matrixToLeech ⟨generatorB, Subgroup.subset_closure (by simp)⟩ *
    matrixToLeech ⟨generatorA, Subgroup.subset_closure (by simp)⟩ *
    icosianHermitianToCo0 yLift

private theorem cubicWord_apply (x : Space) :
    (fullIsometryEquiv cubicWord).val (matrixComparison x) =
      matrixComparison (half stage8 *ᵥ x) := by
  change (fullIsometryEquiv (yIsometry * xIsometry * bIsometry * yIsometry *
    aIsometry * bIsometry * aIsometry * yIsometry)).val (matrixComparison x) = _
  simp only [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  rw [y_apply, a_apply, Matrix.mulVec_mulVec, half_mul _ _ _ word_certificates.1,
    b_apply, Matrix.mulVec_mulVec, half_mul _ _ _ word_certificates.2.1,
    a_apply, Matrix.mulVec_mulVec, half_mul _ _ _ word_certificates.2.2.1,
    y_apply, Matrix.mulVec_mulVec, half_mul _ _ _ word_certificates.2.2.2.1,
    b_apply, Matrix.mulVec_mulVec, half_mul _ _ _ word_certificates.2.2.2.2.1,
    x_apply, Matrix.mulVec_mulVec, half_mul _ _ _ word_certificates.2.2.2.2.2.1,
    y_apply, Matrix.mulVec_mulVec, half_mul _ _ _ word_certificates.2.2.2.2.2.2.1]

/-- The exact integral reference lift is intertwined with the original Eisenstein orientation. -/
theorem cubicWord_cubic (x : Space) :
    (fullIsometryEquiv (icosianHermitianToCo0 referenceLift)).val
      ((fullIsometryEquiv cubicWord).val (matrixComparison x)) =
    (fullIsometryEquiv cubicWord).val
      (matrixComparison (ReferenceBlock.cubicMatrix false *ᵥ x)) := by
  rw [cubicWord_apply, reference_apply, cubicWord_apply,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, block_specifications.2.2]
  have hh := congrArg (fun M => M.map (Int.castRingHom ℚ))
    word_certificates.2.2.2.2.2.2.2
  simp only [Matrix.map_mul] at hh
  unfold half
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hh]

/-- Every factor commutes with each literal integral rational scalar. -/
theorem cubicWord_commute_scalar (u : rationalScalarUnits) :
    Commute cubicWord (icosianScalarsToCo0 u.val) := by
  have hx := (icosianScalars_commute_Hermitian u.val xLift).symm
  have hy := (icosianScalars_commute_Hermitian u.val yLift).symm
  have ha := matrixToLeech_scalar ⟨generatorA, Subgroup.subset_closure (by simp)⟩ u
  have hb := matrixToLeech_scalar ⟨generatorB, Subgroup.subset_closure (by simp)⟩ u
  exact ((((((hy.mul_left hx).mul_left hb).mul_left hy).mul_left ha).mul_left hb).mul_left ha).mul_left hy

/-- Hence the word fixes the entire rational scalar image under conjugation. -/
theorem cubicWord_scalars : ReferenceBlock.scalarImage.map
    (MulAut.conj (leechCentralProjection cubicWord)).toMonoidHom =
      ReferenceBlock.scalarImage := by
  have hc (z : LeechCentralQuotient) (hz : z ∈ ReferenceBlock.scalarImage) :
      (MulAut.conj (leechCentralProjection cubicWord)) z = z := by
    obtain ⟨a, ⟨u, rfl⟩, rfl⟩ := hz
    rw [rationalScalarToFive_projection]
    exact ((cubicWord_commute_scalar u).map leechCentralProjection).mul_inv_cancel
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (MulAut.conj (leechCentralProjection cubicWord)) w ∈ ReferenceBlock.scalarImage
    rw [hc w hw]
    exact hw
  · intro hz
    exact ⟨z, hz, hc z hz⟩

end IntegralAlignment
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
