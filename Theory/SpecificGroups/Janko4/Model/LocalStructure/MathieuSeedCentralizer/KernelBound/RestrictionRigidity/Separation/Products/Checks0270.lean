module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Calibration

/-!
# Quadratic matrix products

Packed multiplication checks products 270 through 314.
Together the batches include every diagonal and every unordered polarized pair.

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


private theorem checks : ∀ (k : Fin 45) (r : Fin 56),
    rowProduct ((basisTransposes.get (productPairs.get ⟨270+k.val, by omega⟩).1).get r)
      (rightProducts.get (productPairs.get ⟨270+k.val, by omega⟩).2) =
        (halfRows (productWords.get ⟨270+k.val, by omega⟩)).get r := by
  simp only [halfRows, get_ofFn]
  decide +kernel

theorem products_270 (k : ℕ) (hl : 270 ≤ k) (hu : k < 315) (hk : k < 1035) :
    decodeHalf (productWords.get ⟨k,hk⟩) =
      (squareBasis (productPairs.get ⟨k,hk⟩).1)ᵀ * testForm *
        squareBasis (productPairs.get ⟨k,hk⟩).2 := by
  have h := checks ⟨k-270, by omega⟩
  have he : 270 + (k-270) = k := by omega
  simp only [he] at h
  have hp := rows_product_eq (k := 56)
    (basisTransposes.get (productPairs.get ⟨k,hk⟩).1)
    (rightProducts.get (productPairs.get ⟨k,hk⟩).2)
    (halfRows (productWords.get ⟨k,hk⟩)) h
  rw [basisTransposes_spec, rightProducts_spec, halfRows_spec, ← Matrix.mul_assoc] at hp
  exact hp.symm

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
