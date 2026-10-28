module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.ConjugationChecks
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.Isometry

/-!
# Exact graph conjugation in the integral Leech block

The checked integer identities intertwine the inverse-adjoint actions of both
source generators with their signed image words. Transport through the actual
lattice comparison proves integral conjugation. Restriction of the same image
matrices modulo two proves precisely J A⁻ᵀ J, including the existing change of
coefficient field. No abstract semidirect product replaces the concrete cover.

Source: Aschbacher, Sporadic Groups (1994), proof of 49.5, p.283.
The concrete matrices and word certificates are documented in `Graph.Data`
and `Graph.Words`, with their ATLAS attribution.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway Atlas.LinearAlgebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
open Block Block.Realization

local instance : CharP GoldenFour 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) GoldenFour).injective 2

private theorem unit_inverse (g : GL (Fin 6) Eisenstein) (M N : SixMatrix)
    (hm : g.val = M) (hn : M*N=1) : g.inv=N := by
  calc
    g.inv = g.inv * 1 := (mul_one _).symm
    _ = g.inv * (g.val * N) := by rw [hm, hn]
    _ = (g.inv * g.val) * N := (mul_assoc _ _ _).symm
    _ = N := by rw [g.inv_val, one_mul]

theorem imageA_action : (rationalAction imageA).val =
    (1/2 : ℚ) • integerMatrix imageANumerator := by
  change realification imageA.val.inv.conjTranspose = _
  rw [unit_inverse imageA.val _ _ imageA_matrix inverseCertificates.1]
  exact actionSpecifications.1

theorem imageB_action : (rationalAction imageB).val =
    (1/2 : ℚ) • integerMatrix imageBNumerator := by
  change realification imageB.val.inv.conjTranspose = _
  rw [unit_inverse imageB.val _ _ imageB_matrix inverseCertificates.2]
  exact actionSpecifications.2

private theorem half_intertwines (P Q : Matrix Index Index ℤ)
    (h : numerator * P = Q * numerator) :
    swapMatrix * ((1/2 : ℚ) • integerMatrix P) =
      ((1/2 : ℚ) • integerMatrix Q) * swapMatrix := by
  have hh := congrArg integerMatrix h
  simp only [map_mul] at hh
  simp only [swapMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hh]

theorem swapMatrix_generatorA : swapMatrix * (rationalAction matrixGeneratorA).val =
    (rationalAction imageA).val * swapMatrix := by
  rw [imageA_action]
  change swapMatrix * realification matrixA.conjTranspose = _
  rw [numeratorA]
  exact half_intertwines _ _ conjugationCertificates.1

theorem swapMatrix_generatorB : swapMatrix * (rationalAction matrixGeneratorB).val =
    (rationalAction imageB).val * swapMatrix := by
  rw [imageB_action]
  change swapMatrix * realification matrixBInv.conjTranspose = _
  rw [numeratorB]
  exact half_intertwines _ _ conjugationCertificates.2

private theorem conjugates_of_matrices (g h : matrixGroup)
    (hm : swapMatrix * (rationalAction g).val = (rationalAction h).val * swapMatrix) :
    swap * matrixToLeech g * swap⁻¹ = matrixToLeech h := by
  have hl : swapLinear * linearAction g = linearAction h * swapLinear := by
    apply LinearEquiv.ext
    intro x
    change swapMatrix *ᵥ ((rationalAction g).val *ᵥ x) =
      (rationalAction h).val *ᵥ (swapMatrix *ᵥ x)
    rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec]
  have hi : swap * matrixToLeech g = matrixToLeech h * swap := by
    apply fullIsometryEquiv.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    change (fullIsometryEquiv swap).val * (fullIsometryEquiv (matrixToLeech g)).val =
      (fullIsometryEquiv (matrixToLeech h)).val * (fullIsometryEquiv swap).val
    rw [swap_extension, matrixToLeech_extension, matrixToLeech_extension]
    change linearAutomorphismCongr matrixComparison swapLinear *
        linearAutomorphismCongr matrixComparison (linearAction g) =
      linearAutomorphismCongr matrixComparison (linearAction h) *
        linearAutomorphismCongr matrixComparison swapLinear
    rw [← map_mul, ← map_mul, hl]
  rw [hi, mul_assoc, mul_inv_cancel, mul_one]

/-- Exact conjugation of the first integral source generator. -/
theorem swap_generatorA : swap * matrixToLeech matrixGeneratorA * swap⁻¹ = matrixToLeech imageA :=
  conjugates_of_matrices _ _ swapMatrix_generatorA

/-- Exact conjugation of the second integral source generator. -/
theorem swap_generatorB : swap * matrixToLeech matrixGeneratorB * swap⁻¹ = matrixToLeech imageB :=
  conjugates_of_matrices _ _ swapMatrix_generatorB

theorem imageA_golden : goldenQuotient imageA = graphTwist threeA := by
  apply (goldenQuotient_eq_iff _ _).mpr
  change (graphTwist threeA).val * modularRows = modularRows * imageA.val.val.map reductionScalars
  rw [imageA_matrix]
  decide +kernel

theorem imageB_golden : goldenQuotient imageB = graphTwist threeB := by
  apply (goldenQuotient_eq_iff _ _).mpr
  change (graphTwist threeB).val * modularRows = modularRows * imageB.val.val.map reductionScalars
  rw [imageB_matrix]
  decide +kernel

/-- The first image word has the literal Peirce graph quotient over `Embedding.F`. -/
theorem imageA_quotient : matrixQuotient imageA = graphTwist (matrixQuotient matrixGeneratorA) := by
  change SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom (goldenQuotient imageA) = _
  rw [imageA_golden, twist_map, matrixQuotient_generatorA]

/-- The second image word has the same exact quotient convention. -/
theorem imageB_quotient : matrixQuotient imageB = graphTwist (matrixQuotient matrixGeneratorB) := by
  change SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom (goldenQuotient imageB) = _
  rw [imageB_golden, twist_map, matrixQuotient_generatorB]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
