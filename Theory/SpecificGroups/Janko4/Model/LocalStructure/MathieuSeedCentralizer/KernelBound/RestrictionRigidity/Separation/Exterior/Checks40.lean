module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 40 through 43 are transported to the original 112-dimensional
coordinates and checked on every one of the 1221 exterior generators.

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

attribute [local irreducible] weights duals embeddingRows embeddingTransposeRows transportMiddles


private theorem transport_40 : flatMatrix (duals.get 40) =
    embedding * decodeHalf (weights.get 40) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 40)) = (transportMiddles.get 40).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 40)) (transportMiddles.get 40) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 40).get i)
      embeddingTransposeRows = flatRow (duals.get 40) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 40) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 40) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 40) i j).symm

private theorem annihilation_40 : ∀ i : Fin 1221,
    flatDot (duals.get 40) (basisFlat i.val) = false := by decide +kernel

private theorem transport_41 : flatMatrix (duals.get 41) =
    embedding * decodeHalf (weights.get 41) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 41)) = (transportMiddles.get 41).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 41)) (transportMiddles.get 41) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 41).get i)
      embeddingTransposeRows = flatRow (duals.get 41) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 41) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 41) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 41) i j).symm

private theorem annihilation_41 : ∀ i : Fin 1221,
    flatDot (duals.get 41) (basisFlat i.val) = false := by decide +kernel

private theorem transport_42 : flatMatrix (duals.get 42) =
    embedding * decodeHalf (weights.get 42) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 42)) = (transportMiddles.get 42).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 42)) (transportMiddles.get 42) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 42).get i)
      embeddingTransposeRows = flatRow (duals.get 42) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 42) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 42) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 42) i j).symm

private theorem annihilation_42 : ∀ i : Fin 1221,
    flatDot (duals.get 42) (basisFlat i.val) = false := by decide +kernel

private theorem transport_43 : flatMatrix (duals.get 43) =
    embedding * decodeHalf (weights.get 43) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 43)) = (transportMiddles.get 43).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 43)) (transportMiddles.get 43) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 43).get i)
      embeddingTransposeRows = flatRow (duals.get 43) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 43) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 43) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 43) i j).symm

private theorem annihilation_43 : ∀ i : Fin 1221,
    flatDot (duals.get 43) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_40 (k : ℕ) (hl : 40 ≤ k) (hu : k < 44) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_40, annihilation_40⟩
  · exact ⟨transport_41, annihilation_41⟩
  · exact ⟨transport_42, annihilation_42⟩
  · exact ⟨transport_43, annihilation_43⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
