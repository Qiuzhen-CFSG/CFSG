module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density.RankOne
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density.Spanning

import Mathlib.Tactic.FinCases

/-!
# The column and row orbits span

The sixteen columns of P are successive left generator translates of v;
the sixteen rows of Q are successive right translates of λ. Each recurrence
is checked on all sixteen entries. The two dense inverse checks give
`P Pi = 1` and `Qi Q = 1`, exactly the sides consumed by the outer-product
spanning argument. Hence every subalgebra containing the literal A and B
contains all matrices. No group action or irreducibility premise is used.

Source matrices and attribution: ATLAS L33G1-f16r16aB0 in
`SixteenModels.Data`; witness search reproduced in `Density/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density

theorem column_zero : (fun k => P k 0) = v :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_zero : Q 0 = lam :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_1 : codeMulVec codesA (fun k => P k 0) = (fun k => P k 1) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_2 : codeMulVec codesB (fun k => P k 1) = (fun k => P k 2) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_3 : codeMulVec codesA (fun k => P k 2) = (fun k => P k 3) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_4 : codeMulVec codesB (fun k => P k 3) = (fun k => P k 4) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_5 : codeMulVec codesA (fun k => P k 4) = (fun k => P k 5) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_6 : codeMulVec codesB (fun k => P k 4) = (fun k => P k 6) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_7 : codeMulVec codesA (fun k => P k 6) = (fun k => P k 7) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_8 : codeMulVec codesB (fun k => P k 5) = (fun k => P k 8) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_9 : codeMulVec codesA (fun k => P k 8) = (fun k => P k 9) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_10 : codeMulVec codesB (fun k => P k 7) = (fun k => P k 10) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_11 : codeMulVec codesB (fun k => P k 8) = (fun k => P k 11) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_12 : codeMulVec codesA (fun k => P k 10) = (fun k => P k 12) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_13 : codeMulVec codesA (fun k => P k 11) = (fun k => P k 13) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_14 : codeMulVec codesB (fun k => P k 9) = (fun k => P k 14) :=
  checkVector_sound _ _ (by decide +kernel)

theorem column_step_15 : codeMulVec codesA (fun k => P k 14) = (fun k => P k 15) :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_1 : codeVecMul (Q 0) codesA = Q 1 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_2 : codeVecMul (Q 0) codesB = Q 2 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_3 : codeVecMul (Q 2) codesA = Q 3 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_4 : codeVecMul (Q 3) codesB = Q 4 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_5 : codeVecMul (Q 4) codesA = Q 5 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_6 : codeVecMul (Q 4) codesB = Q 6 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_7 : codeVecMul (Q 5) codesB = Q 7 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_8 : codeVecMul (Q 6) codesA = Q 8 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_9 : codeVecMul (Q 7) codesA = Q 9 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_10 : codeVecMul (Q 7) codesB = Q 10 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_11 : codeVecMul (Q 8) codesB = Q 11 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_12 : codeVecMul (Q 9) codesB = Q 12 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_13 : codeVecMul (Q 10) codesA = Q 13 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_14 : codeVecMul (Q 11) codesA = Q 14 :=
  checkVector_sound _ _ (by decide +kernel)

theorem row_step_15 : codeVecMul (Q 12) codesA = Q 15 :=
  checkVector_sound _ _ (by decide +kernel)

theorem inverse_P : codeProduct P Pi = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem inverse_Q : codeProduct Qi Q = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

variable {F : Type*} [Field F] [CharP F 2]

theorem column_reachable (t : F) (ht : t ^ 4 = t + 1)
    (S : Subalgebra F (Matrix (Fin 16) (Fin 16) F))
    (ha : matrixA t ∈ S) (hb : matrixB t ∈ S) (i : Fin 16) :
    ∃ W ∈ S, W.mulVec (evalVector t v) = fun k => evalMatrix t P k i := by
  have step (i j : Fin 16) (M : Matrix (Fin 16) (Fin 16) (Fin 16))
      (hM : evalMatrix t M ∈ S)
      (h : codeMulVec M (fun k => P k j) = fun k => P k i)
      (hj : ∃ W ∈ S, W.mulVec (evalVector t v) = fun k => evalMatrix t P k j) :
      ∃ W ∈ S, W.mulVec (evalVector t v) = fun k => evalMatrix t P k i := by
    obtain ⟨W, hW, hWv⟩ := hj
    refine ⟨evalMatrix t M * W, S.mul_mem hM hW, ?_⟩
    rw [← Matrix.mulVec_mulVec, hWv]
    change (evalMatrix t M).mulVec (evalVector t (fun k => P k j)) =
      evalVector t (fun k => P k i)
    rw [← eval_mulVec t ht, h]
  have h0 : ∃ W ∈ S, W.mulVec (evalVector t v) = fun k => evalMatrix t P k 0 := by
    refine ⟨1, S.one_mem, ?_⟩
    rw [Matrix.one_mulVec]
    exact congrArg (evalVector t) column_zero.symm
  have h1 := step 1 0 codesA ha column_step_1 h0
  have h2 := step 2 1 codesB hb column_step_2 h1
  have h3 := step 3 2 codesA ha column_step_3 h2
  have h4 := step 4 3 codesB hb column_step_4 h3
  have h5 := step 5 4 codesA ha column_step_5 h4
  have h6 := step 6 4 codesB hb column_step_6 h4
  have h7 := step 7 6 codesA ha column_step_7 h6
  have h8 := step 8 5 codesB hb column_step_8 h5
  have h9 := step 9 8 codesA ha column_step_9 h8
  have h10 := step 10 7 codesB hb column_step_10 h7
  have h11 := step 11 8 codesB hb column_step_11 h8
  have h12 := step 12 10 codesA ha column_step_12 h10
  have h13 := step 13 11 codesA ha column_step_13 h11
  have h14 := step 14 9 codesB hb column_step_14 h9
  have h15 := step 15 14 codesA ha column_step_15 h14
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

theorem row_reachable (t : F) (ht : t ^ 4 = t + 1)
    (S : Subalgebra F (Matrix (Fin 16) (Fin 16) F))
    (ha : matrixA t ∈ S) (hb : matrixB t ∈ S) (i : Fin 16) :
    ∃ W ∈ S, Matrix.vecMul (evalVector t lam) W = evalMatrix t Q i := by
  have step (i j : Fin 16) (M : Matrix (Fin 16) (Fin 16) (Fin 16))
      (hM : evalMatrix t M ∈ S)
      (h : codeVecMul (Q j) M = Q i)
      (hj : ∃ W ∈ S, Matrix.vecMul (evalVector t lam) W = evalMatrix t Q j) :
      ∃ W ∈ S, Matrix.vecMul (evalVector t lam) W = evalMatrix t Q i := by
    obtain ⟨W, hW, hWv⟩ := hj
    refine ⟨W * evalMatrix t M, S.mul_mem hW hM, ?_⟩
    rw [← Matrix.vecMul_vecMul, hWv]
    change Matrix.vecMul (evalVector t (Q j)) (evalMatrix t M) = evalVector t (Q i)
    rw [← eval_vecMul t ht, h]
  have h0 : ∃ W ∈ S, Matrix.vecMul (evalVector t lam) W = evalMatrix t Q 0 := by
    refine ⟨1, S.one_mem, ?_⟩
    rw [Matrix.vecMul_one]
    exact congrArg (evalVector t) row_zero.symm
  have h1 := step 1 0 codesA ha row_step_1 h0
  have h2 := step 2 0 codesB hb row_step_2 h0
  have h3 := step 3 2 codesA ha row_step_3 h2
  have h4 := step 4 3 codesB hb row_step_4 h3
  have h5 := step 5 4 codesA ha row_step_5 h4
  have h6 := step 6 4 codesB hb row_step_6 h4
  have h7 := step 7 5 codesB hb row_step_7 h5
  have h8 := step 8 6 codesA ha row_step_8 h6
  have h9 := step 9 7 codesA ha row_step_9 h7
  have h10 := step 10 7 codesB hb row_step_10 h7
  have h11 := step 11 8 codesB hb row_step_11 h8
  have h12 := step 12 9 codesB hb row_step_12 h9
  have h13 := step 13 10 codesA ha row_step_13 h10
  have h14 := step 14 11 codesA ha row_step_14 h11
  have h15 := step 15 12 codesA ha row_step_15 h12
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- Concrete application of all certificates to the literal generated algebra. -/
theorem subalgebra_eq_top (t : F) (ht : t ^ 4 = t + 1)
    (S : Subalgebra F (Matrix (Fin 16) (Fin 16) F))
    (ha : matrixA t ∈ S) (hb : matrixB t ∈ S) : S = ⊤ := by
  apply top_of_rankOne S (evalVector t v) (evalVector t lam)
    (evalMatrix t P) (evalMatrix t Pi) (evalMatrix t Q) (evalMatrix t Qi)
    (rankOne_mem t ht S ha hb) (column_reachable t ht S ha hb) (row_reachable t ht S ha hb)
  · rw [← eval_product t ht, inverse_P, eval_one]
  · rw [← eval_product t ht, inverse_Q, eval_one]

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density
