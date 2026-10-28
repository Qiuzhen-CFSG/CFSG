module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

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


theorem rightProductRows_check : ∀ (i : Fin 45) (r : Fin 56), rowProduct ((halfRows testFormWord).get r)
      (halfRows (alternativeBasisWords.get ⟨i.val+11, by omega⟩)) = (rightProducts.get i).get r := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
