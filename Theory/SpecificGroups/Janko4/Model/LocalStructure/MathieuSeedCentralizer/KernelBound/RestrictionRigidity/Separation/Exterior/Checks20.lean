module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 20 through 24 are transported to the original 112-dimensional
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


private theorem transport_20 : flatMatrix (duals.get 20) =
    embedding * decodeHalf (weights.get 20) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 20)) = (transportMiddles.get 20).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 20)) (transportMiddles.get 20) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 20).get i)
      embeddingTransposeRows = flatRow (duals.get 20) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 20) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 20) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 20) i j).symm

private theorem annihilation_20 : ∀ i : Fin 1221,
    flatDot (duals.get 20) (basisFlat i.val) = false := by decide +kernel

private theorem transport_21 : flatMatrix (duals.get 21) =
    embedding * decodeHalf (weights.get 21) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 21)) = (transportMiddles.get 21).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 21)) (transportMiddles.get 21) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 21).get i)
      embeddingTransposeRows = flatRow (duals.get 21) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 21) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 21) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 21) i j).symm

private theorem annihilation_21 : ∀ i : Fin 1221,
    flatDot (duals.get 21) (basisFlat i.val) = false := by decide +kernel

private theorem transport_22 : flatMatrix (duals.get 22) =
    embedding * decodeHalf (weights.get 22) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 22)) = (transportMiddles.get 22).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 22)) (transportMiddles.get 22) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 22).get i)
      embeddingTransposeRows = flatRow (duals.get 22) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 22) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 22) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 22) i j).symm

private theorem annihilation_22 : ∀ i : Fin 1221,
    flatDot (duals.get 22) (basisFlat i.val) = false := by decide +kernel

private theorem transport_23 : flatMatrix (duals.get 23) =
    embedding * decodeHalf (weights.get 23) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 23)) = (transportMiddles.get 23).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 23)) (transportMiddles.get 23) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 23).get i)
      embeddingTransposeRows = flatRow (duals.get 23) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 23) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 23) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 23) i j).symm

private theorem annihilation_23 : ∀ i : Fin 1221,
    flatDot (duals.get 23) (basisFlat i.val) = false := by decide +kernel

private theorem transport_24 : flatMatrix (duals.get 24) =
    embedding * decodeHalf (weights.get 24) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 24)) = (transportMiddles.get 24).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 24)) (transportMiddles.get 24) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 24).get i)
      embeddingTransposeRows = flatRow (duals.get 24) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 24) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 24) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 24) i j).symm

private theorem annihilation_24 : ∀ i : Fin 1221,
    flatDot (duals.get 24) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_20 (k : ℕ) (hl : 20 ≤ k) (hu : k < 25) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_20, annihilation_20⟩
  · exact ⟨transport_21, annihilation_21⟩
  · exact ⟨transport_22, annihilation_22⟩
  · exact ⟨transport_23, annihilation_23⟩
  · exact ⟨transport_24, annihilation_24⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
