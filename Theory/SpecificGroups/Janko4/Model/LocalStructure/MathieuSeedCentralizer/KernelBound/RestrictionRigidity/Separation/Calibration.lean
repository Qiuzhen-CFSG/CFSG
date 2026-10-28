module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Calibration.BasisRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Calibration.RightRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Calibration.RightTransposeRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Calibration.LinearRows

/-!
# Calibration of the actual basis and linear terms

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
set_option Elab.async false

attribute [local irreducible] squareBasis testForm topOperator basisTransposes rightProducts linearWords
  testFormWord topOperatorWord alternativeBasisWords weights duals productPairs productWords
  embeddingRows embeddingTransposeRows transportMiddles sourceWord sourceMask sourceMiddle topRight topLinearWord
  rightTransposes weightTransposes

theorem basisTransposes_spec (i : Fin 45) :
    rowsMatrix (n := 56) (basisTransposes.get i) = (squareBasis i)ᵀ := by

  have ht := transposeRows_of_check
    (halfRows (alternativeBasisWords.get ⟨i.val+11, by omega⟩)) (basisTransposes.get i) (basisTransposeRows_check i)
  rw [halfRows_spec] at ht
  simpa only [squareBasis, alternativeBasis] using ht

theorem rightProducts_spec (i : Fin 45) : rowsMatrix (n := 56) (rightProducts.get i) = testForm * squareBasis i := by

  have hh := rows_product_eq (k := 56) (halfRows testFormWord)
    (halfRows (alternativeBasisWords.get ⟨i.val+11, by omega⟩)) (rightProducts.get i) (rightProductRows_check i)
  rw [halfRows_spec, halfRows_spec] at hh
  change decodeHalf testFormWord * decodeHalf (alternativeBasisWords.get ⟨i.val+11, by omega⟩) = _ at hh
  simpa only [testForm, squareBasis, alternativeBasis] using hh.symm

theorem rightTransposes_spec (i : Fin 45) :
    rowsMatrix (n := 56) (rightTransposes.get i) = (rowsMatrix (n := 56) (rightProducts.get i))ᵀ := by

  exact transposeRows_of_check _ _ (rightTransposeRows_check i)

theorem linearWords_spec (i : Fin 45) :
    decodeHalf (linearWords.get i) = linearTerm testForm (squareBasis i) := by

  have ht := addRows_of_check (n := 56) (rightTransposes.get i) (rightProducts.get i)
    (halfRows (linearWords.get i)) (linearWordRows_check i)
  rw [halfRows_spec, rightTransposes_spec, rightProducts_spec, transpose_mul, testForm_transpose] at ht
  exact ht

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
