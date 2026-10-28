module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Transport and exterior annihilation checks

Functionals 30 through 34 are transported to the original 112-dimensional
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


private theorem transport_30 : flatMatrix (duals.get 30) =
    embedding * decodeHalf (weights.get 30) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 30)) = (transportMiddles.get 30).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 30)) (transportMiddles.get 30) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 30).get i)
      embeddingTransposeRows = flatRow (duals.get 30) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 30) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 30) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 30) i j).symm

private theorem annihilation_30 : ∀ i : Fin 1221,
    flatDot (duals.get 30) (basisFlat i.val) = false := by decide +kernel

private theorem transport_31 : flatMatrix (duals.get 31) =
    embedding * decodeHalf (weights.get 31) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 31)) = (transportMiddles.get 31).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 31)) (transportMiddles.get 31) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 31).get i)
      embeddingTransposeRows = flatRow (duals.get 31) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 31) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 31) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 31) i j).symm

private theorem annihilation_31 : ∀ i : Fin 1221,
    flatDot (duals.get 31) (basisFlat i.val) = false := by decide +kernel

private theorem transport_32 : flatMatrix (duals.get 32) =
    embedding * decodeHalf (weights.get 32) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 32)) = (transportMiddles.get 32).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 32)) (transportMiddles.get 32) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 32).get i)
      embeddingTransposeRows = flatRow (duals.get 32) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 32) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 32) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 32) i j).symm

private theorem annihilation_32 : ∀ i : Fin 1221,
    flatDot (duals.get 32) (basisFlat i.val) = false := by decide +kernel

private theorem transport_33 : flatMatrix (duals.get 33) =
    embedding * decodeHalf (weights.get 33) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 33)) = (transportMiddles.get 33).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 33)) (transportMiddles.get 33) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 33).get i)
      embeddingTransposeRows = flatRow (duals.get 33) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 33) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 33) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 33) i j).symm

private theorem annihilation_33 : ∀ i : Fin 1221,
    flatDot (duals.get 33) (basisFlat i.val) = false := by decide +kernel

private theorem transport_34 : flatMatrix (duals.get 34) =
    embedding * decodeHalf (weights.get 34) * embeddingᵀ := by
  rw [← embeddingTransposeRows_spec, ← embeddingRows_spec, ← halfRows_spec]
  have h1 : ∀ i : Fin 112, rowProduct (embeddingRows.get i)
      (halfRows (weights.get 34)) = (transportMiddles.get 34).get i := by
    simp only [rowProduct, halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingRows (halfRows (weights.get 34)) (transportMiddles.get 34) h1]
  have h2 : ∀ i : Fin 112, rowProduct ((transportMiddles.get 34).get i)
      embeddingTransposeRows = flatRow (duals.get 34) i.val := by decide +kernel
  rw [rows_product_eq (transportMiddles.get 34) embeddingTransposeRows
    (Vector.ofFn (fun i : Fin 112 => flatRow (duals.get 34) i.val)) (by simpa only [get_ofFn] using h2)]
  funext i j
  simp only [rowsMatrix, get_ofFn]
  exact (flatRow_bit (duals.get 34) i j).symm

private theorem annihilation_34 : ∀ i : Fin 1221,
    flatDot (duals.get 34) (basisFlat i.val) = false := by decide +kernel

theorem exterior_checks_30 (k : ℕ) (hl : 30 ≤ k) (hu : k < 35) (hk : k < 45) :
    flatMatrix (duals.get ⟨k,hk⟩) = embedding * decodeHalf (weights.get ⟨k,hk⟩) * embeddingᵀ ∧
    ∀ i : Fin 1221, flatDot (duals.get ⟨k,hk⟩) (basisFlat i.val) = false := by
  interval_cases k
  · exact ⟨transport_30, annihilation_30⟩
  · exact ⟨transport_31, annihilation_31⟩
  · exact ⟨transport_32, annihilation_32⟩
  · exact ⟨transport_33, annihilation_33⟩
  · exact ⟨transport_34, annihilation_34⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
