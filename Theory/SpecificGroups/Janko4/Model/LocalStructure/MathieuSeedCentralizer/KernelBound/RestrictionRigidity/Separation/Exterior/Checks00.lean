module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 0 through 4 are transported to the original 112-dimensional
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


private theorem transport_0 : flatMatrix (duals.get 0) =
    embedding * decodeHalf (weights.get 0) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 0)) = (transportMiddles.get 0).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 0)) (transportMiddles.get 0) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 0).get i)
      embeddingTransposeRows = flatRow (duals.get 0) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 0) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 0) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 0) i j).symm

private theorem annihilation_0 : ∀ i : Fin 1221,
    flatDot (duals.get 0) (basisFlat i.val) = false := by decide +kernel

private theorem transport_1 : flatMatrix (duals.get 1) =
    embedding * decodeHalf (weights.get 1) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 1)) = (transportMiddles.get 1).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 1)) (transportMiddles.get 1) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 1).get i)
      embeddingTransposeRows = flatRow (duals.get 1) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 1) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 1) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 1) i j).symm

private theorem annihilation_1 : ∀ i : Fin 1221,
    flatDot (duals.get 1) (basisFlat i.val) = false := by decide +kernel

private theorem transport_2 : flatMatrix (duals.get 2) =
    embedding * decodeHalf (weights.get 2) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 2)) = (transportMiddles.get 2).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 2)) (transportMiddles.get 2) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 2).get i)
      embeddingTransposeRows = flatRow (duals.get 2) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 2) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 2) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 2) i j).symm

private theorem annihilation_2 : ∀ i : Fin 1221,
    flatDot (duals.get 2) (basisFlat i.val) = false := by decide +kernel

private theorem transport_3 : flatMatrix (duals.get 3) =
    embedding * decodeHalf (weights.get 3) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 3)) = (transportMiddles.get 3).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 3)) (transportMiddles.get 3) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 3).get i)
      embeddingTransposeRows = flatRow (duals.get 3) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 3) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 3) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 3) i j).symm

private theorem annihilation_3 : ∀ i : Fin 1221,
    flatDot (duals.get 3) (basisFlat i.val) = false := by decide +kernel

private theorem transport_4 : flatMatrix (duals.get 4) =
    embedding * decodeHalf (weights.get 4) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 4)) = (transportMiddles.get 4).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 4)) (transportMiddles.get 4) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 4).get i)
      embeddingTransposeRows = flatRow (duals.get 4) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 4) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 4) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 4) i j).symm

private theorem annihilation_4 : ∀ i : Fin 1221,
    flatDot (duals.get 4) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_0 (k : ℕ) (hl : 0 ≤ k) (hu : k < 5) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_0, annihilation_0⟩
  · exact ⟨transport_1, annihilation_1⟩
  · exact ⟨transport_2, annihilation_2⟩
  · exact ⟨transport_3, annihilation_3⟩
  · exact ⟨transport_4, annihilation_4⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
