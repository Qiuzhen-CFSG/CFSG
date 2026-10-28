module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Rank bounds and minors over a field

A matrix has rank at most `r` exactly when every square submatrix of size
`r + 1` has zero determinant. The converse selects independent columns and
then independent rows; this works in every characteristic and in the empty
cases. These are the linear-algebraic rank equations for the flag variety
used in Borel, *Linear Algebraic Groups*, §11.1.
-/

@[expose] public noncomputable section

open Module
namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus

universe u v w
variable {k : Type u} [Field k] {m : Type v} {n : Type w}
variable [Fintype m] [Fintype n]

private theorem exists_independent_rows (A : Matrix m n k) (q : ℕ) (hq : q ≤ A.rank) :
    ∃ r : Fin q → m, LinearIndependent k (fun i => A (r i)) := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' k A.row
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = A.rank := by
    rw [A.rank_eq_finrank_span_row, ← hs]
    exact linearIndependent_iff_card_eq_finrank_span.mp hi
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin q) ≤ Fintype.card κ by simpa [hc] using hq)
  exact ⟨a ∘ e, hi.comp e e.injective⟩

/-- Every size up to the rank occurs as the size of a nonzero minor. -/
theorem exists_nonzero_minor (A : Matrix m n k) (q : ℕ) (hq : q ≤ A.rank) :
    ∃ (r : Fin q → m) (c : Fin q → n), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_independent_rows A.transpose q (by simpa using hq)
  let B := A.submatrix id c
  have hB : B.rank = q := by
    exact (Matrix.rank_transpose B).symm.trans
      (hc.rank_matrix.trans (Fintype.card_fin q))
  obtain ⟨r, hr⟩ := exists_independent_rows B q (by omega)
  have hcol : LinearIndependent k (A.submatrix r c).transpose.col := hr
  have hunit : IsUnit (A.submatrix r c).transpose :=
    Matrix.mulVec_injective_iff_isUnit.mp (Matrix.mulVec_injective_iff.mpr hcol)
  refine ⟨r, c, ?_⟩
  simpa only [Matrix.det_transpose] using
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

/-- Rank at most `r` is equivalent to vanishing of all minors of size `r + 1`.
Repeated rows or columns are allowed, so no separate injectivity guards are needed. -/
theorem rank_le_iff_minors (A : Matrix m n k) (r : ℕ) :
    A.rank ≤ r ↔ ∀ (a : Fin (r+1) → m) (b : Fin (r+1) → n),
      (A.submatrix a b).det = 0 := by
  classical
  constructor
  · intro h a b
    by_contra hdet
    have hsub := Matrix.rank_submatrix_le A a b
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hsub
    omega
  · intro h
    by_contra hgt
    obtain ⟨a, b, hab⟩ := exists_nonzero_minor A (r+1) (by omega)
    exact hab (h a b)

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
