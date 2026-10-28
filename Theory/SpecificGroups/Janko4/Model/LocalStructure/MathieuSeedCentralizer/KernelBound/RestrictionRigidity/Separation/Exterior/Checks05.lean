module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 5 through 9 are transported to the original 112-dimensional
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


private theorem transport_5 : flatMatrix (duals.get 5) =
    embedding * decodeHalf (weights.get 5) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 5)) = (transportMiddles.get 5).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 5)) (transportMiddles.get 5) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 5).get i)
      embeddingTransposeRows = flatRow (duals.get 5) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 5) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 5) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 5) i j).symm

private theorem annihilation_5 : ∀ i : Fin 1221,
    flatDot (duals.get 5) (basisFlat i.val) = false := by decide +kernel

private theorem transport_6 : flatMatrix (duals.get 6) =
    embedding * decodeHalf (weights.get 6) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 6)) = (transportMiddles.get 6).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 6)) (transportMiddles.get 6) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 6).get i)
      embeddingTransposeRows = flatRow (duals.get 6) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 6) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 6) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 6) i j).symm

private theorem annihilation_6 : ∀ i : Fin 1221,
    flatDot (duals.get 6) (basisFlat i.val) = false := by decide +kernel

private theorem transport_7 : flatMatrix (duals.get 7) =
    embedding * decodeHalf (weights.get 7) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 7)) = (transportMiddles.get 7).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 7)) (transportMiddles.get 7) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 7).get i)
      embeddingTransposeRows = flatRow (duals.get 7) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 7) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 7) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 7) i j).symm

private theorem annihilation_7 : ∀ i : Fin 1221,
    flatDot (duals.get 7) (basisFlat i.val) = false := by decide +kernel

private theorem transport_8 : flatMatrix (duals.get 8) =
    embedding * decodeHalf (weights.get 8) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 8)) = (transportMiddles.get 8).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 8)) (transportMiddles.get 8) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 8).get i)
      embeddingTransposeRows = flatRow (duals.get 8) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 8) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 8) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 8) i j).symm

private theorem annihilation_8 : ∀ i : Fin 1221,
    flatDot (duals.get 8) (basisFlat i.val) = false := by decide +kernel

private theorem transport_9 : flatMatrix (duals.get 9) =
    embedding * decodeHalf (weights.get 9) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 9)) = (transportMiddles.get 9).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 9)) (transportMiddles.get 9) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 9).get i)
      embeddingTransposeRows = flatRow (duals.get 9) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 9) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 9) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 9) i j).symm

private theorem annihilation_9 : ∀ i : Fin 1221,
    flatDot (duals.get 9) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_5 (k : ℕ) (hl : 5 ≤ k) (hu : k < 10) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_5, annihilation_5⟩
  · exact ⟨transport_6, annihilation_6⟩
  · exact ⟨transport_7, annihilation_7⟩
  · exact ⟨transport_8, annihilation_8⟩
  · exact ⟨transport_9, annihilation_9⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
