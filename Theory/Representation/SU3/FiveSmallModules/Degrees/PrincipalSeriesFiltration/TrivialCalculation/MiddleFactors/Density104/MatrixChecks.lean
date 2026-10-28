module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density104.Witnesses
import Mathlib.Tactic.FinCases

/-!
# Checked orbit edges, transposes, and inverses for the degree-104 factor

Packed vector products check the orbit edges. Transpose entries are checked in
batches of thirteen rows, keeping each kernel reduction small. Two packed
matrix products certify the spanning bases. These finite identities are kept
separate from the orbit induction so that proof assembly does not repeat them.
Source motivation: Guralnick–Malle Proposition 4.3; Aschbacher–Smith K.2, p.453.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density104Certificate
open Thompson.BinaryMatrix CycleCertificate

private theorem all_rows (P : Fin 104 → Prop)
    (h : ∀ (b : Fin 8) (r : Fin 13), P ⟨13 * b.val + r.val, by omega⟩) : ∀ i, P i := by
  intro i
  let b : Fin 8 := ⟨i.val / 13, by omega⟩
  let r : Fin 13 := ⟨i.val % 13, by omega⟩
  have he : (⟨13 * b.val + r.val, by omega⟩ : Fin 104) = i := by
    apply Fin.ext
    change 13 * (i.val / 13) + i.val % 13 = i.val
    omega
  exact he ▸ h b r

private theorem transpose_bits_0_0 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 0 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 0 + r.val) := by
  decide +kernel

private theorem transpose_bits_0_1 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 1 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 1 + r.val) := by
  decide +kernel

private theorem transpose_bits_0_2 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 2 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 2 + r.val) := by
  decide +kernel

private theorem transpose_bits_0_3 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 3 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 3 + r.val) := by
  decide +kernel

private theorem transpose_bits_0_4 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 4 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 4 + r.val) := by
  decide +kernel

private theorem transpose_bits_0_5 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 5 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 5 + r.val) := by
  decide +kernel

private theorem transpose_bits_0_6 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 6 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 6 + r.val) := by
  decide +kernel

private theorem transpose_bits_0_7 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 0)[13 * 7 + r.val]!.testBit j.val =
      (factorRows104 0)[j.val]!.testBit (13 * 7 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_0 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 0 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 0 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_1 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 1 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 1 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_2 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 2 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 2 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_3 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 3 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 3 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_4 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 4 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 4 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_5 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 5 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 5 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_6 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 6 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 6 + r.val) := by
  decide +kernel

private theorem transpose_bits_1_7 : ∀ (r : Fin 13) (j : Fin 104),
    (transposedActors 1)[13 * 7 + r.val]!.testBit j.val =
      (factorRows104 1)[j.val]!.testBit (13 * 7 + r.val) := by
  decide +kernel

private theorem transpose_bits (a : Fin 2) : ∀ i j : Fin 104,
    (transposedActors a)[i.val]!.testBit j.val = (factorRows104 a)[j.val]!.testBit i.val := by
  apply all_rows
  intro b r
  fin_cases a <;> fin_cases b
  · exact transpose_bits_0_0 r
  · exact transpose_bits_0_1 r
  · exact transpose_bits_0_2 r
  · exact transpose_bits_0_3 r
  · exact transpose_bits_0_4 r
  · exact transpose_bits_0_5 r
  · exact transpose_bits_0_6 r
  · exact transpose_bits_0_7 r
  · exact transpose_bits_1_0 r
  · exact transpose_bits_1_1 r
  · exact transpose_bits_1_2 r
  · exact transpose_bits_1_3 r
  · exact transpose_bits_1_4 r
  · exact transpose_bits_1_5 r
  · exact transpose_bits_1_6 r
  · exact transpose_bits_1_7 r

theorem transposed_actors (a : Fin 2) :
    decode 104 (transposedActors a) = (factor104 a).transpose := by
  ext i j
  change bit (transposedActors a)[i.val]! j.val = bit (factorRows104 a)[j.val]! i.val
  unfold bit
  rw [transpose_bits]

private theorem column_bits_0 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 0 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 0 + r.val) := by
  decide +kernel

private theorem column_bits_1 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 1 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 1 + r.val) := by
  decide +kernel

private theorem column_bits_2 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 2 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 2 + r.val) := by
  decide +kernel

private theorem column_bits_3 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 3 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 3 + r.val) := by
  decide +kernel

private theorem column_bits_4 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 4 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 4 + r.val) := by
  decide +kernel

private theorem column_bits_5 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 5 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 5 + r.val) := by
  decide +kernel

private theorem column_bits_6 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 6 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 6 + r.val) := by
  decide +kernel

private theorem column_bits_7 : ∀ (r : Fin 13) (j : Fin 104),
    columnVectors[13 * 7 + r.val]!.testBit j.val = columns[j.val]!.testBit (13 * 7 + r.val) := by
  decide +kernel

private theorem column_bits : ∀ i j : Fin 104,
    columnVectors[i.val]!.testBit j.val = columns[j.val]!.testBit i.val := by
  apply all_rows
  intro b r
  fin_cases b
  · exact column_bits_0 r
  · exact column_bits_1 r
  · exact column_bits_2 r
  · exact column_bits_3 r
  · exact column_bits_4 r
  · exact column_bits_5 r
  · exact column_bits_6 r
  · exact column_bits_7 r

theorem column_entries (i j : Fin 104) :
    bit columnVectors[i.val]! j.val = decode 104 columns j i := by
  change bit columnVectors[i.val]! j.val = bit columns[j.val]! i.val
  unfold bit
  rw [column_bits]

theorem column_parent_lt : ∀ i : Fin 103, columnParent i < i.succ := by
  decide +kernel

theorem row_parent_lt : ∀ i : Fin 103, rowParent i < i.succ := by
  decide +kernel

theorem column_step : ∀ i : Fin 103,
    rowProduct columnVectors[(columnParent i).val]! (transposedActors (columnActor i)) 104 =
      columnVectors[i.succ.val]! := by
  decide +kernel

theorem row_step : ∀ i : Fin 103,
    rowProduct rows[(rowParent i).val]! (factorRows104 (rowActor i)) 104 = rows[i.succ.val]! := by
  decide +kernel

/-- A checked right inverse for the matrix of column translates. -/
theorem columns_inverse : decode 104 columns * decode 104 columnInverse = 1 :=
  decode_mul_one 104 columns columnInverse (by decide +kernel)

/-- A checked left inverse for the matrix of row translates. -/
theorem rows_inverse : decode 104 rowInverse * decode 104 rows = 1 :=
  decode_mul_one 104 rowInverse rows (by decide +kernel)

theorem column_initial : columnVectors[0]! = column := rfl

theorem row_initial : rows[0]! = row := rfl

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Density104Certificate
