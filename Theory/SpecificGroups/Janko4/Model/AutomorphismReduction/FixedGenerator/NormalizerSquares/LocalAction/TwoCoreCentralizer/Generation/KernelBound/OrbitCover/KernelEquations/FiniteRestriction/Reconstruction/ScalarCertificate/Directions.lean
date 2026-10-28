module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.CoefficientChecks
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Matrices
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Algebra

/-! The checked row products represent the two Frobenius functionals on all
pairs of published affine directions. Symmetry of their Gram matrix eliminates
quadratic cross terms over F₂; the diagonal and linear terms give the defect.
Source and witness conventions: ScalarCertificate/source/README.md. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

private theorem direction_decode (k : Fin 124) :
    (decode (affineDirectionRows.get k) : RestrictionMatrix) = affineDirection k := rfl


theorem direction_weight (k : Fin 124) :
    restrictionPairing * affineDirection k * decode functionalJBits +
      restrictionTestForm 0 * affineDirection k * decode functionalEBits =
      (decode (directionWeights.get k) : RestrictionMatrix) := by
  have hj1 := decodeRows_product (n := 50) (p := 50) _ _ _ (first_j_check k)
  have he1 := decodeRows_product (n := 50) (p := 50) _ _ _ (first_e_check k)
  have hj2 := decodeRows_product (n := 50) (p := 50) _ _ _ (second_j_check k)
  have he2 := decodeRows_product (n := 50) (p := 50) _ _ _ (second_e_check k)
  simp only [decode_rows, j_decode, e_decode, direction_decode] at hj1 he1
  simp only [decode_rows, fj_decode, fe_decode] at hj2 he2
  rw [hj1, he1, hj2, he2, ← decode_xor, weight_check]


theorem identity_weight :
    restrictionPairing * decode functionalJBits +
      restrictionTestForm 0 * decode functionalEBits =
      (decode identityWeightBits : RestrictionMatrix) := by
  rw [← j_decode, ← e_decode, ← fj_decode, ← fe_decode,
    decodeRows_product _ _ _ identity_j_check, decodeRows_product _ _ _ identity_e_check]
  funext i j
  exact identity_weight_check i j


private theorem identity_decode : (decode identityBits : RestrictionMatrix) = 1 := by
  funext i j
  exact identity_check i j


set_option exponentiation.threshold 2500 in
theorem bilinear_direction (i j : Fin 124) :
    bilinear (affineDirection i) (affineDirection j) = bit (gramRows.get i) j.val := by
  rw [bilinear_weight, j_transpose, e_transpose, direction_weight, ← direction_decode]
  rw [pairing_decode (m := 50) (n := 50) (k := 12) _ _ ((Nat.and_le_left).trans_lt (weight_bound i))
    (show 50 * 50 ≤ 2 ^ 12 by decide)]
  exact gram_check i j


theorem bilinear_direction_symmetric (i j : Fin 124) :
    bilinear (affineDirection i) (affineDirection j) =
      bilinear (affineDirection j) (affineDirection i) := by
  rw [bilinear_direction, bilinear_direction, gram_symmetric]


set_option exponentiation.threshold 2500 in
theorem direction_polynomial (k : Fin 124) :
    bilinear (affineDirection k) (affineDirection k) +
      bilinear 1 (affineDirection k) + bilinear (affineDirection k) 1 =
      bit 17552799707978362774193210816690218843 k.val := by
  rw [bilinear_direction, bilinear_weight 1, bilinear_weight (affineDirection k) 1,
    j_transpose, e_transpose, Matrix.mul_one, Matrix.mul_one, identity_weight, direction_weight,
    ← direction_decode, ← identity_decode]
  rw [pairing_decode (m := 50) (n := 50) (k := 12) _ _ ((Nat.and_le_left).trans_lt identity_weight_bound)
    (show 50 * 50 ≤ 2 ^ 12 by decide),
    pairing_decode (m := 50) (n := 50) (k := 12) _ _ ((Nat.and_le_left).trans_lt (weight_bound k))
    (show 50 * 50 ≤ 2 ^ 12 by decide)]
  exact linear_check k


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
