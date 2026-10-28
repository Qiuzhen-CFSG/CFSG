module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Nonzero evaluation minors

A finite linearly independent family of functions admits a square evaluation
minor with nonzero determinant. The proof views the functions as the rows of
a rectangular matrix, selects a basis from its columns, and reindexes that
basis by the original finite index type. This is the finite linear-algebra
input used to turn modular trace independence into a separating evaluation.
-/

namespace Matrix

noncomputable section

variable {R ι X : Type*} [Field R] [Fintype ι] [DecidableEq ι] [Fintype X]

/-- A finite linearly independent family of functions has a nonzero square
matrix of evaluations. -/
public theorem exists_eval_det_ne_zero (f : ι → X → R)
    (fli : LinearIndependent R f) :
    ∃ x : ι → X, (Matrix.of fun i j => f i (x j)).det ≠ 0 := by
  classical
  let A : Matrix ι X R := Matrix.of f
  have hrows : LinearIndependent R A.row := by
    simpa [A] using fli
  have hrank : A.rank = Fintype.card ι := hrows.rank_matrix
  obtain ⟨s, hs, hscard, hsspan, hsli⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn R (Set.range A.col)
  have hspanrank : Module.finrank R (Submodule.span R (Set.range A.col)) = Fintype.card ι := by
    rw [← hrank, A.rank_eq_finrank_span_cols]
  have hsubcard : Fintype.card s = Fintype.card ι := by
    rw [Fintype.card_coe, hscard, hspanrank]
  choose g hg using fun a : s => hs a.property
  let e : ι ≃ s := Fintype.equivOfCardEq hsubcard.symm
  let B : Matrix ι ι R := Matrix.of fun i j => A i (g (e j))
  have hBcols : LinearIndependent R B.col := by
    have hsel : LinearIndependent R (fun a : s => A.col (g a)) := by
      simpa [hg] using hsli.linearIndependent
    have hsel' : LinearIndependent R (fun j : ι => A.col (g (e j))) :=
      hsel.comp e (Equiv.injective e)
    convert hsel' using 1
    ext j i
    rfl
  have hdet : B.det ≠ 0 := by
    have hunit : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.mp hBcols
    exact (Matrix.isUnit_iff_isUnit_det B).mp hunit |>.ne_zero
  refine ⟨fun j => g (e j), ?_⟩
  simpa [B, A] using hdet

end
end Matrix
