module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 10 through 14 are transported to the original 112-dimensional
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


private theorem transport_10 : flatMatrix (duals.get 10) =
    embedding * decodeHalf (weights.get 10) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 10)) = (transportMiddles.get 10).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 10)) (transportMiddles.get 10) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 10).get i)
      embeddingTransposeRows = flatRow (duals.get 10) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 10) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 10) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 10) i j).symm

private theorem annihilation_10 : ∀ i : Fin 1221,
    flatDot (duals.get 10) (basisFlat i.val) = false := by decide +kernel

private theorem transport_11 : flatMatrix (duals.get 11) =
    embedding * decodeHalf (weights.get 11) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 11)) = (transportMiddles.get 11).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 11)) (transportMiddles.get 11) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 11).get i)
      embeddingTransposeRows = flatRow (duals.get 11) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 11) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 11) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 11) i j).symm

private theorem annihilation_11 : ∀ i : Fin 1221,
    flatDot (duals.get 11) (basisFlat i.val) = false := by decide +kernel

private theorem transport_12 : flatMatrix (duals.get 12) =
    embedding * decodeHalf (weights.get 12) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 12)) = (transportMiddles.get 12).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 12)) (transportMiddles.get 12) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 12).get i)
      embeddingTransposeRows = flatRow (duals.get 12) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 12) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 12) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 12) i j).symm

private theorem annihilation_12 : ∀ i : Fin 1221,
    flatDot (duals.get 12) (basisFlat i.val) = false := by decide +kernel

private theorem transport_13 : flatMatrix (duals.get 13) =
    embedding * decodeHalf (weights.get 13) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 13)) = (transportMiddles.get 13).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 13)) (transportMiddles.get 13) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 13).get i)
      embeddingTransposeRows = flatRow (duals.get 13) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 13) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 13) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 13) i j).symm

private theorem annihilation_13 : ∀ i : Fin 1221,
    flatDot (duals.get 13) (basisFlat i.val) = false := by decide +kernel

private theorem transport_14 : flatMatrix (duals.get 14) =
    embedding * decodeHalf (weights.get 14) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 14)) = (transportMiddles.get 14).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 14)) (transportMiddles.get 14) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 14).get i)
      embeddingTransposeRows = flatRow (duals.get 14) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 14) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 14) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 14) i j).symm

private theorem annihilation_14 : ∀ i : Fin 1221,
    flatDot (duals.get 14) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_10 (k : ℕ) (hl : 10 ≤ k) (hu : k < 15) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_10, annihilation_10⟩
  · exact ⟨transport_11, annihilation_11⟩
  · exact ⟨transport_12, annihilation_12⟩
  · exact ⟨transport_13, annihilation_13⟩
  · exact ⟨transport_14, annihilation_14⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
