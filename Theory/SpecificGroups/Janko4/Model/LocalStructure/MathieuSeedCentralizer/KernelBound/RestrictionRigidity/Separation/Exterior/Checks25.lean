module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 25 through 29 are transported to the original 112-dimensional
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


private theorem transport_25 : flatMatrix (duals.get 25) =
    embedding * decodeHalf (weights.get 25) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 25)) = (transportMiddles.get 25).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 25)) (transportMiddles.get 25) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 25).get i)
      embeddingTransposeRows = flatRow (duals.get 25) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 25) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 25) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 25) i j).symm

private theorem annihilation_25 : ∀ i : Fin 1221,
    flatDot (duals.get 25) (basisFlat i.val) = false := by decide +kernel

private theorem transport_26 : flatMatrix (duals.get 26) =
    embedding * decodeHalf (weights.get 26) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 26)) = (transportMiddles.get 26).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 26)) (transportMiddles.get 26) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 26).get i)
      embeddingTransposeRows = flatRow (duals.get 26) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 26) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 26) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 26) i j).symm

private theorem annihilation_26 : ∀ i : Fin 1221,
    flatDot (duals.get 26) (basisFlat i.val) = false := by decide +kernel

private theorem transport_27 : flatMatrix (duals.get 27) =
    embedding * decodeHalf (weights.get 27) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 27)) = (transportMiddles.get 27).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 27)) (transportMiddles.get 27) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 27).get i)
      embeddingTransposeRows = flatRow (duals.get 27) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 27) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 27) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 27) i j).symm

private theorem annihilation_27 : ∀ i : Fin 1221,
    flatDot (duals.get 27) (basisFlat i.val) = false := by decide +kernel

private theorem transport_28 : flatMatrix (duals.get 28) =
    embedding * decodeHalf (weights.get 28) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 28)) = (transportMiddles.get 28).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 28)) (transportMiddles.get 28) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 28).get i)
      embeddingTransposeRows = flatRow (duals.get 28) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 28) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 28) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 28) i j).symm

private theorem annihilation_28 : ∀ i : Fin 1221,
    flatDot (duals.get 28) (basisFlat i.val) = false := by decide +kernel

private theorem transport_29 : flatMatrix (duals.get 29) =
    embedding * decodeHalf (weights.get 29) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 29)) = (transportMiddles.get 29).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 29)) (transportMiddles.get 29) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 29).get i)
      embeddingTransposeRows = flatRow (duals.get 29) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 29) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 29) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 29) i j).symm

private theorem annihilation_29 : ∀ i : Fin 1221,
    flatDot (duals.get 29) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_25 (k : ℕ) (hl : 25 ≤ k) (hu : k < 30) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_25, annihilation_25⟩
  · exact ⟨transport_26, annihilation_26⟩
  · exact ⟨transport_27, annihilation_27⟩
  · exact ⟨transport_28, annihilation_28⟩
  · exact ⟨transport_29, annihilation_29⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
