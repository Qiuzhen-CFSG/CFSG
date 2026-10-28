module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Data

/-! Closed binary arithmetic for the scalar certificate. The direction products
are checked in four blocks to limit kernel memory. The resulting row products,
Gram matrix, and linear coefficients are interpreted in Directions.
Source and witness conventions: ScalarCertificate/source/README.md. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

private instance finForall {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := Nat.decidableForallFin P

/-- Force the packed row once before the bit selections. This avoids repeated
normalization of a matrix-row extraction during kernel reduction. -/
def forcedRow {n : ℕ} (x : ℕ) (ys : Vector ℕ n) : ℕ :=
  match x with
  | 0 => rowProduct 0 ys
  | t + 1 => rowProduct (t + 1) ys

theorem forcedRow_eq {n : ℕ} (x : ℕ) (ys : Vector ℕ n) :
    forcedRow x ys = rowProduct x ys := by cases x <;> rfl

theorem all_direction_blocks {P : Fin 124 → Prop}
    (h0 : ∀ t : Fin 31, P ⟨t.val, by omega⟩)
    (h1 : ∀ t : Fin 31, P ⟨31 + t.val, by omega⟩)
    (h2 : ∀ t : Fin 31, P ⟨62 + t.val, by omega⟩)
    (h3 : ∀ t : Fin 31, P ⟨93 + t.val, by omega⟩) :
    ∀ k : Fin 124, P k := by
  intro k
  by_cases hlt0 : k.val < 31
  · exact h0 ⟨k.val, hlt0⟩
  by_cases hlt1 : k.val < 62
  · have h := h1 ⟨k.val - 31, by omega⟩
    have he : (⟨31 + (k.val - 31), by omega⟩ : Fin 124) = k := by
      apply Fin.ext
      change 31 + (k.val - 31) = k.val
      omega
    exact he ▸ h
  by_cases hlt2 : k.val < 93
  · have h := h2 ⟨k.val - 62, by omega⟩
    have he : (⟨62 + (k.val - 62), by omega⟩ : Fin 124) = k := by
      apply Fin.ext
      change 62 + (k.val - 62) = k.val
      omega
    exact he ▸ h
  · have h := h3 ⟨k.val - 93, by omega⟩
    have he : (⟨93 + (k.val - 93), by omega⟩ : Fin 124) = k := by
      apply Fin.ext
      change 93 + (k.val - 93) = k.val
      omega
    exact he ▸ h



end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
