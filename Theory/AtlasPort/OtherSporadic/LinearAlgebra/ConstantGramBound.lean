/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/LinearAlgebra/ConstantGramBound.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Fintype.Option

/-!
# Dimension bound for a constant Gram family

Augmented rational matrices supply a left inverse and hence the dimension bound.

Source: Gerald Höhn, ATLAS, `Atlas/LinearAlgebra/ConstantGramBound.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

noncomputable section
namespace Atlas.LinearAlgebra
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A constant off-diagonal Gram family occupies at least n-1 dimensions.
The augmented matrices give a left inverse without any spectral theorem. -/
theorem constant_gram_card_bound {I D : Type*} [Fintype I] [Fintype D]
    (v : I → D → ℚ) (q b : ℚ) (hqb : q ≠ b)
    (hgram : ∀ i j, ∑ k, v i k * v j k = if i = j then q else b) :
    Fintype.card I ≤ Fintype.card D + 1 := by
  classical
  let A : Matrix I (Option D) ℚ := fun i k =>
    match k with | none => -b / (q-b) | some k => v i k / (q-b)
  let B : Matrix (Option D) I ℚ := fun k j =>
    match k with | none => 1 | some k => v j k
  have hne : q-b ≠ 0 := sub_ne_zero.mpr hqb
  have hAB : A*B = 1 := by
    ext i j
    change (∑ k : Option D, A i k * B k j) = if i = j then 1 else 0
    simp only [Fintype.sum_option,A,B]
    have hs : (∑ k, v i k / (q-b) * v j k) = (∑ k, v i k * v j k) / (q-b) := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs,hgram]
    by_cases hij : i = j
    · subst j
      simp only [ite_true,mul_one]
      field_simp
      ring
    · simp only [if_neg hij,mul_one]
      ring
  have hh := Matrix.rank_mul_le_left A B
  rw [hAB,Matrix.rank_one] at hh
  exact hh.trans ((Matrix.rank_le_card_width A).trans (by simp))

end Atlas.LinearAlgebra
