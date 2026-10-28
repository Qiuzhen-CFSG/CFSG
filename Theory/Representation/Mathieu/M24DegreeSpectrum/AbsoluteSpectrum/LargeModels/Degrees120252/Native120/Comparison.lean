module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.ComparisonData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Certificate

/-!
# Checked comparison of the binary degree-120 matrices

The saved comparison sends native adjoint coordinates to the literal ATLAS
column coordinates. Packed row operations are decoded by the existing matrix
certificate theorem. Every identity below is kernel checked.

Sources: `source/adjoint120-comparison.json`; James, J. Algebra 27 (1973),
57–111; GM02, Proposition 5.1. The JSON is data only, not a proof premise.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open MatrixChecks FactorAlgebras.Certificate

set_option Elab.async false

private theorem packed_product {n : ℕ} (xs ys : List ℕ)
    (hx : xs.length = n) (hy : ys.length = n) :
    packedMatrix (n := n) xs * packedMatrix ys = packedMatrix (xs.map (combineList ys)) :=
  matrix_product xs ys _ hy (product_rows xs ys _ hx rfl)

private theorem packed_identity (n : ℕ) :
    packedMatrix (n := n) ((List.range n).map (2 ^ ·)) = 1 := by
  ext i j
  simp [packedMatrix, Nat.testBit_two_pow, Matrix.one_apply, Fin.val_inj]

private theorem inverse_rows :
    comparisonRows.map (combineList inverseRows) = (List.range 120).map (2 ^ ·) := by
  decide +kernel

/-- The stored inverse is checked on the literal packed comparison. -/
theorem comparison_mul_inverse : comparisonMatrix * inverseMatrix = 1 := by
  rw [comparisonMatrix, inverseMatrix, packed_product _ _ (by decide) (by decide),
    inverse_rows, packed_identity]

private theorem inverse_rows_left :
    inverseRows.map (combineList comparisonRows) = (List.range 120).map (2 ^ ·) := by
  decide +kernel

/-- The other multiplication order is checked directly as well. -/
theorem inverse_mul_comparison : inverseMatrix * comparisonMatrix = 1 := by
  rw [inverseMatrix, comparisonMatrix, packed_product _ _ (by decide) (by decide),
    inverse_rows_left, packed_identity]

private theorem intertwining_left0_batch0 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 0)) =
      entry intertwiningRows0 (i.val + 0) := by
  decide +kernel

private theorem intertwining_left0_batch1 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 10)) =
      entry intertwiningRows0 (i.val + 10) := by
  decide +kernel

private theorem intertwining_left0_batch2 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 20)) =
      entry intertwiningRows0 (i.val + 20) := by
  decide +kernel

private theorem intertwining_left0_batch3 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 30)) =
      entry intertwiningRows0 (i.val + 30) := by
  decide +kernel

private theorem intertwining_left0_batch4 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 40)) =
      entry intertwiningRows0 (i.val + 40) := by
  decide +kernel

private theorem intertwining_left0_batch5 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 50)) =
      entry intertwiningRows0 (i.val + 50) := by
  decide +kernel

private theorem intertwining_left0_batch6 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 60)) =
      entry intertwiningRows0 (i.val + 60) := by
  decide +kernel

private theorem intertwining_left0_batch7 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 70)) =
      entry intertwiningRows0 (i.val + 70) := by
  decide +kernel

private theorem intertwining_left0_batch8 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 80)) =
      entry intertwiningRows0 (i.val + 80) := by
  decide +kernel

private theorem intertwining_left0_batch9 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 90)) =
      entry intertwiningRows0 (i.val + 90) := by
  decide +kernel

private theorem intertwining_left0_batch10 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 100)) =
      entry intertwiningRows0 (i.val + 100) := by
  decide +kernel

private theorem intertwining_left0_batch11 : ∀ i : Fin 10,
    combineList adjointRows0 (entry comparisonRows (i.val + 110)) =
      entry intertwiningRows0 (i.val + 110) := by
  decide +kernel

private theorem intertwining_left0 (i : Fin 120) :
    combineList adjointRows0 (entry comparisonRows i.val) = entry intertwiningRows0 i.val := by
  let q : Fin 12 := ⟨i.val / 10, by omega⟩
  let r : Fin 10 := ⟨i.val % 10, by omega⟩
  have hi : i.val = r.val + 10 * q.val := by dsimp [q, r]; omega
  clear_value q r
  fin_cases q
  · have he : i.val = r.val + 0 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch0 r
  · have he : i.val = r.val + 10 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch1 r
  · have he : i.val = r.val + 20 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch2 r
  · have he : i.val = r.val + 30 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch3 r
  · have he : i.val = r.val + 40 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch4 r
  · have he : i.val = r.val + 50 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch5 r
  · have he : i.val = r.val + 60 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch6 r
  · have he : i.val = r.val + 70 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch7 r
  · have he : i.val = r.val + 80 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch8 r
  · have he : i.val = r.val + 90 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch9 r
  · have he : i.val = r.val + 100 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch10 r
  · have he : i.val = r.val + 110 := by simpa using hi
    rw [he]
    exact intertwining_left0_batch11 r

private theorem intertwining_right0_batch0 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 0)) =
      entry intertwiningRows0 (i.val + 0) := by
  decide +kernel

private theorem intertwining_right0_batch1 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 10)) =
      entry intertwiningRows0 (i.val + 10) := by
  decide +kernel

private theorem intertwining_right0_batch2 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 20)) =
      entry intertwiningRows0 (i.val + 20) := by
  decide +kernel

private theorem intertwining_right0_batch3 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 30)) =
      entry intertwiningRows0 (i.val + 30) := by
  decide +kernel

private theorem intertwining_right0_batch4 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 40)) =
      entry intertwiningRows0 (i.val + 40) := by
  decide +kernel

private theorem intertwining_right0_batch5 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 50)) =
      entry intertwiningRows0 (i.val + 50) := by
  decide +kernel

private theorem intertwining_right0_batch6 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 60)) =
      entry intertwiningRows0 (i.val + 60) := by
  decide +kernel

private theorem intertwining_right0_batch7 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 70)) =
      entry intertwiningRows0 (i.val + 70) := by
  decide +kernel

private theorem intertwining_right0_batch8 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 80)) =
      entry intertwiningRows0 (i.val + 80) := by
  decide +kernel

private theorem intertwining_right0_batch9 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 90)) =
      entry intertwiningRows0 (i.val + 90) := by
  decide +kernel

private theorem intertwining_right0_batch10 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 100)) =
      entry intertwiningRows0 (i.val + 100) := by
  decide +kernel

private theorem intertwining_right0_batch11 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_0 (i.val + 110)) =
      entry intertwiningRows0 (i.val + 110) := by
  decide +kernel

private theorem intertwining_right0 (i : Fin 120) :
    combineList comparisonRows (entry rows120_0 i.val) = entry intertwiningRows0 i.val := by
  let q : Fin 12 := ⟨i.val / 10, by omega⟩
  let r : Fin 10 := ⟨i.val % 10, by omega⟩
  have hi : i.val = r.val + 10 * q.val := by dsimp [q, r]; omega
  clear_value q r
  fin_cases q
  · have he : i.val = r.val + 0 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch0 r
  · have he : i.val = r.val + 10 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch1 r
  · have he : i.val = r.val + 20 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch2 r
  · have he : i.val = r.val + 30 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch3 r
  · have he : i.val = r.val + 40 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch4 r
  · have he : i.val = r.val + 50 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch5 r
  · have he : i.val = r.val + 60 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch6 r
  · have he : i.val = r.val + 70 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch7 r
  · have he : i.val = r.val + 80 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch8 r
  · have he : i.val = r.val + 90 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch9 r
  · have he : i.val = r.val + 100 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch10 r
  · have he : i.val = r.val + 110 := by simpa using hi
    rw [he]
    exact intertwining_right0_batch11 r

private theorem intertwining_left1_batch0 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 0)) =
      entry intertwiningRows1 (i.val + 0) := by
  decide +kernel

private theorem intertwining_left1_batch1 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 10)) =
      entry intertwiningRows1 (i.val + 10) := by
  decide +kernel

private theorem intertwining_left1_batch2 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 20)) =
      entry intertwiningRows1 (i.val + 20) := by
  decide +kernel

private theorem intertwining_left1_batch3 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 30)) =
      entry intertwiningRows1 (i.val + 30) := by
  decide +kernel

private theorem intertwining_left1_batch4 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 40)) =
      entry intertwiningRows1 (i.val + 40) := by
  decide +kernel

private theorem intertwining_left1_batch5 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 50)) =
      entry intertwiningRows1 (i.val + 50) := by
  decide +kernel

private theorem intertwining_left1_batch6 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 60)) =
      entry intertwiningRows1 (i.val + 60) := by
  decide +kernel

private theorem intertwining_left1_batch7 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 70)) =
      entry intertwiningRows1 (i.val + 70) := by
  decide +kernel

private theorem intertwining_left1_batch8 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 80)) =
      entry intertwiningRows1 (i.val + 80) := by
  decide +kernel

private theorem intertwining_left1_batch9 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 90)) =
      entry intertwiningRows1 (i.val + 90) := by
  decide +kernel

private theorem intertwining_left1_batch10 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 100)) =
      entry intertwiningRows1 (i.val + 100) := by
  decide +kernel

private theorem intertwining_left1_batch11 : ∀ i : Fin 10,
    combineList adjointRows1 (entry comparisonRows (i.val + 110)) =
      entry intertwiningRows1 (i.val + 110) := by
  decide +kernel

private theorem intertwining_left1 (i : Fin 120) :
    combineList adjointRows1 (entry comparisonRows i.val) = entry intertwiningRows1 i.val := by
  let q : Fin 12 := ⟨i.val / 10, by omega⟩
  let r : Fin 10 := ⟨i.val % 10, by omega⟩
  have hi : i.val = r.val + 10 * q.val := by dsimp [q, r]; omega
  clear_value q r
  fin_cases q
  · have he : i.val = r.val + 0 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch0 r
  · have he : i.val = r.val + 10 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch1 r
  · have he : i.val = r.val + 20 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch2 r
  · have he : i.val = r.val + 30 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch3 r
  · have he : i.val = r.val + 40 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch4 r
  · have he : i.val = r.val + 50 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch5 r
  · have he : i.val = r.val + 60 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch6 r
  · have he : i.val = r.val + 70 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch7 r
  · have he : i.val = r.val + 80 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch8 r
  · have he : i.val = r.val + 90 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch9 r
  · have he : i.val = r.val + 100 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch10 r
  · have he : i.val = r.val + 110 := by simpa using hi
    rw [he]
    exact intertwining_left1_batch11 r

private theorem intertwining_right1_batch0 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 0)) =
      entry intertwiningRows1 (i.val + 0) := by
  decide +kernel

private theorem intertwining_right1_batch1 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 10)) =
      entry intertwiningRows1 (i.val + 10) := by
  decide +kernel

private theorem intertwining_right1_batch2 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 20)) =
      entry intertwiningRows1 (i.val + 20) := by
  decide +kernel

private theorem intertwining_right1_batch3 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 30)) =
      entry intertwiningRows1 (i.val + 30) := by
  decide +kernel

private theorem intertwining_right1_batch4 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 40)) =
      entry intertwiningRows1 (i.val + 40) := by
  decide +kernel

private theorem intertwining_right1_batch5 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 50)) =
      entry intertwiningRows1 (i.val + 50) := by
  decide +kernel

private theorem intertwining_right1_batch6 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 60)) =
      entry intertwiningRows1 (i.val + 60) := by
  decide +kernel

private theorem intertwining_right1_batch7 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 70)) =
      entry intertwiningRows1 (i.val + 70) := by
  decide +kernel

private theorem intertwining_right1_batch8 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 80)) =
      entry intertwiningRows1 (i.val + 80) := by
  decide +kernel

private theorem intertwining_right1_batch9 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 90)) =
      entry intertwiningRows1 (i.val + 90) := by
  decide +kernel

private theorem intertwining_right1_batch10 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 100)) =
      entry intertwiningRows1 (i.val + 100) := by
  decide +kernel

private theorem intertwining_right1_batch11 : ∀ i : Fin 10,
    combineList comparisonRows (entry rows120_1 (i.val + 110)) =
      entry intertwiningRows1 (i.val + 110) := by
  decide +kernel

private theorem intertwining_right1 (i : Fin 120) :
    combineList comparisonRows (entry rows120_1 i.val) = entry intertwiningRows1 i.val := by
  let q : Fin 12 := ⟨i.val / 10, by omega⟩
  let r : Fin 10 := ⟨i.val % 10, by omega⟩
  have hi : i.val = r.val + 10 * q.val := by dsimp [q, r]; omega
  clear_value q r
  fin_cases q
  · have he : i.val = r.val + 0 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch0 r
  · have he : i.val = r.val + 10 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch1 r
  · have he : i.val = r.val + 20 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch2 r
  · have he : i.val = r.val + 30 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch3 r
  · have he : i.val = r.val + 40 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch4 r
  · have he : i.val = r.val + 50 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch5 r
  · have he : i.val = r.val + 60 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch6 r
  · have he : i.val = r.val + 70 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch7 r
  · have he : i.val = r.val + 80 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch8 r
  · have he : i.val = r.val + 90 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch9 r
  · have he : i.val = r.val + 100 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch10 r
  · have he : i.val = r.val + 110 := by simpa using hi
    rw [he]
    exact intertwining_right1_batch11 r

/-- The direction is C · native = ATLAS · C, with column action. -/
theorem comparison_intertwines (j : Fin 2) :
    comparisonMatrix * adjointMatrix j = matrix120 j * comparisonMatrix := by
  fin_cases j
  · change packedMatrix comparisonRows * packedMatrix adjointRows0 =
      packedMatrix rows120_0 * packedMatrix comparisonRows
    exact (matrix_product comparisonRows adjointRows0 intertwiningRows0
      (by decide) intertwining_left0).trans
      (matrix_product rows120_0 comparisonRows intertwiningRows0
        (by decide) intertwining_right0).symm
  · change packedMatrix comparisonRows * packedMatrix adjointRows1 =
      packedMatrix rows120_1 * packedMatrix comparisonRows
    exact (matrix_product comparisonRows adjointRows1 intertwiningRows1
      (by decide) intertwining_left1).trans
      (matrix_product rows120_1 comparisonRows intertwiningRows1
        (by decide) intertwining_right1).symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
