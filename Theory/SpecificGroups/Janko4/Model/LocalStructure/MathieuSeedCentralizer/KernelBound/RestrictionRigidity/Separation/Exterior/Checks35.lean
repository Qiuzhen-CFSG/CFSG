module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 35 through 39 are transported to the original 112-dimensional
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


private theorem transport_35 : flatMatrix (duals.get 35) =
    embedding * decodeHalf (weights.get 35) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 35)) = (transportMiddles.get 35).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 35)) (transportMiddles.get 35) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 35).get i)
      embeddingTransposeRows = flatRow (duals.get 35) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 35) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 35) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 35) i j).symm

private theorem annihilation_35 : ∀ i : Fin 1221,
    flatDot (duals.get 35) (basisFlat i.val) = false := by decide +kernel

private theorem transport_36 : flatMatrix (duals.get 36) =
    embedding * decodeHalf (weights.get 36) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 36)) = (transportMiddles.get 36).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 36)) (transportMiddles.get 36) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 36).get i)
      embeddingTransposeRows = flatRow (duals.get 36) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 36) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 36) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 36) i j).symm

private theorem annihilation_36 : ∀ i : Fin 1221,
    flatDot (duals.get 36) (basisFlat i.val) = false := by decide +kernel

private theorem transport_37 : flatMatrix (duals.get 37) =
    embedding * decodeHalf (weights.get 37) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 37)) = (transportMiddles.get 37).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 37)) (transportMiddles.get 37) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 37).get i)
      embeddingTransposeRows = flatRow (duals.get 37) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 37) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 37) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 37) i j).symm

private theorem annihilation_37 : ∀ i : Fin 1221,
    flatDot (duals.get 37) (basisFlat i.val) = false := by decide +kernel

private theorem transport_38 : flatMatrix (duals.get 38) =
    embedding * decodeHalf (weights.get 38) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 38)) = (transportMiddles.get 38).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 38)) (transportMiddles.get 38) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 38).get i)
      embeddingTransposeRows = flatRow (duals.get 38) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 38) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 38) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 38) i j).symm

private theorem annihilation_38 : ∀ i : Fin 1221,
    flatDot (duals.get 38) (basisFlat i.val) = false := by decide +kernel

private theorem transport_39 : flatMatrix (duals.get 39) =
    embedding * decodeHalf (weights.get 39) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 39)) = (transportMiddles.get 39).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 39)) (transportMiddles.get 39) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 39).get i)
      embeddingTransposeRows = flatRow (duals.get 39) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 39) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 39) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 39) i j).symm

private theorem annihilation_39 : ∀ i : Fin 1221,
    flatDot (duals.get 39) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_35 (k : ℕ) (hl : 35 ≤ k) (hu : k < 40) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_35, annihilation_35⟩
  · exact ⟨transport_36, annihilation_36⟩
  · exact ⟨transport_37, annihilation_37⟩
  · exact ⟨transport_38, annihilation_38⟩
  · exact ⟨transport_39, annihilation_39⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
