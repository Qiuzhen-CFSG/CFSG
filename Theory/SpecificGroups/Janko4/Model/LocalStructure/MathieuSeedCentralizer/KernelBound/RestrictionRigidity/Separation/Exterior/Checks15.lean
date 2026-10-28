module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 15 through 19 are transported to the original 112-dimensional
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


private theorem transport_15 : flatMatrix (duals.get 15) =
    embedding * decodeHalf (weights.get 15) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 15)) = (transportMiddles.get 15).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 15)) (transportMiddles.get 15) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 15).get i)
      embeddingTransposeRows = flatRow (duals.get 15) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 15) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 15) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 15) i j).symm

private theorem annihilation_15 : ∀ i : Fin 1221,
    flatDot (duals.get 15) (basisFlat i.val) = false := by decide +kernel

private theorem transport_16 : flatMatrix (duals.get 16) =
    embedding * decodeHalf (weights.get 16) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 16)) = (transportMiddles.get 16).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 16)) (transportMiddles.get 16) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 16).get i)
      embeddingTransposeRows = flatRow (duals.get 16) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 16) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 16) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 16) i j).symm

private theorem annihilation_16 : ∀ i : Fin 1221,
    flatDot (duals.get 16) (basisFlat i.val) = false := by decide +kernel

private theorem transport_17 : flatMatrix (duals.get 17) =
    embedding * decodeHalf (weights.get 17) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 17)) = (transportMiddles.get 17).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 17)) (transportMiddles.get 17) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 17).get i)
      embeddingTransposeRows = flatRow (duals.get 17) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 17) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 17) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 17) i j).symm

private theorem annihilation_17 : ∀ i : Fin 1221,
    flatDot (duals.get 17) (basisFlat i.val) = false := by decide +kernel

private theorem transport_18 : flatMatrix (duals.get 18) =
    embedding * decodeHalf (weights.get 18) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 18)) = (transportMiddles.get 18).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 18)) (transportMiddles.get 18) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 18).get i)
      embeddingTransposeRows = flatRow (duals.get 18) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 18) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 18) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 18) i j).symm

private theorem annihilation_18 : ∀ i : Fin 1221,
    flatDot (duals.get 18) (basisFlat i.val) = false := by decide +kernel

private theorem transport_19 : flatMatrix (duals.get 19) =
    embedding * decodeHalf (weights.get 19) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 19)) = (transportMiddles.get 19).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 19)) (transportMiddles.get 19) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 19).get i)
      embeddingTransposeRows = flatRow (duals.get 19) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 19) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 19) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 19) i j).symm

private theorem annihilation_19 : ∀ i : Fin 1221,
    flatDot (duals.get 19) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_15 (k : ℕ) (hl : 15 ≤ k) (hu : k < 20) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_15, annihilation_15⟩
  · exact ⟨transport_16, annihilation_16⟩
  · exact ⟨transport_17, annihilation_17⟩
  · exact ⟨transport_18, annihilation_18⟩
  · exact ⟨transport_19, annihilation_19⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
