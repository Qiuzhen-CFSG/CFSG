module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Rejection of the actual top-operator linear term

Every displayed matrix identity is checked using ordinary kernel reduction.

Source: KernelBound/source/README.md and kernel-restriction.json. Numerical
witnesses are checked by Lean; the generator is not trusted.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

set_option maxRecDepth 10000
attribute [local irreducible] testForm topOperator weights duals topRight topLinearWord
  testFormWord topOperatorWord embeddingRows embeddingTransposeRows transportMiddles

private theorem topLinearWord_spec : decodeHalf topLinearWord = linearTerm testForm topOperator := by
  have hprod : testForm * topOperator = rowsMatrix (n := 56) topRight := by
    have h : ∀ r : Fin 56, rowProduct ((halfRows testFormWord).get r)
        (halfRows topOperatorWord) = topRight.get r := by
      simp only [rowProduct, halfRows, get_ofFn]
      decide +kernel
    simpa only [halfRows_spec, testForm, topOperator] using rows_product_eq (k := 56)
      (halfRows testFormWord) (halfRows topOperatorWord) topRight h
  have h : decodeHalf topLinearWord = (rowsMatrix (n := 56) topRight)ᵀ + rowsMatrix topRight := by
    decide +kernel
  rw [h, ← hprod, transpose_mul, testForm_transpose]
  rfl

private theorem rejection_transport : flatMatrix (duals.get 44) =
    embedding * decodeHalf (weights.get 44) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 44)) = (transportMiddles.get 44).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 44)) (transportMiddles.get 44) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 44).get i)
      embeddingTransposeRows = flatRow (duals.get 44) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 44) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 44) i.val))
    (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 44) i j).symm

private theorem rejection_annihilation : ∀ i : Fin 1221,
    flatDot (duals.get 44) (basisFlat i.val) = false := by decide +kernel

private theorem rejection_value : halfDot (weights.get 44) topLinearWord = 1 := by decide +kernel

theorem top_rejected : linearTerm testForm topOperator ∉ restrictionSpace := by
  intro h
  have hz := functional_restriction_zero_of_dual _ _ rejection_transport rejection_annihilation h
  rw [← topLinearWord_spec, functional_decode, rejection_value] at hz
  exact one_ne_zero hz

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
