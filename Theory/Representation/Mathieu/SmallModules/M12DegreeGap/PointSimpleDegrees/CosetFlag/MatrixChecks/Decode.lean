module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.Predicates

/-!
# Decoding the eleven-coset matrix certificates

Recursive XOR is matrix multiplication over F₂. A shifted zero column has no
entries below its block, and extracting a binary slice preserves exactly its
diagonal entries. Every coordinate belongs to a layer since the cuts start
at zero and end at 720. These lemmas connect the packed certificates to all
four literal fields of `MatrixIdentities`.

Source: James, J. Algebra 27 (1973), 57–111; witness conventions in
`PointSimpleDegrees/source/README.md`.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
open Data
open Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration

private theorem originalColumns_length (s : Fin 2) : (originalColumns s).length = 720 := by
  revert s
  decide +kernel

private theorem packed_cosetMatrix (s : Fin 2) :
    Packed.matrix (originalColumns s) = cosetMatrix s := by
  ext r j
  have hsize : (Witness.leftAction[s.val]!).size = 720 := by
    revert s
    decide +kernel
  simp [Packed.matrix, originalColumns, Packed.bit, cosetMatrix,
    hsize, j.isLt, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

private theorem packed_basisMatrix : Packed.matrix Witness.basisColumns.toList = basisMatrix := by
  ext r j
  simp only [Packed.matrix, basisMatrix, Array.getElem!_toList, Packed.bit, bit]

private theorem packed_inverseMatrix : Packed.matrix Witness.inverseColumns.toList = inverseMatrix := by
  ext r j
  simp only [Packed.matrix, inverseMatrix, Array.getElem!_toList, Packed.bit, bit]

private theorem packed_actionMatrix (s : Fin 2) :
    Packed.matrix (Witness.adaptedColumns[s.val]!).toList = actionMatrix s := by
  ext r j
  simp only [Packed.matrix, actionMatrix, Array.getElem!_toList, Packed.bit, bit]

theorem inverse_of_columns (h : ∀ j : Fin 720, columnCertificate j.val) :
    inverseMatrix * basisMatrix = 1 := by
  rw [← packed_inverseMatrix, ← packed_basisMatrix]
  apply Packed.matrix_mul_one
  · decide +kernel
  · intro j
    simpa only [Array.getElem!_toList] using (h j).1

theorem action_of_columns (h : ∀ j : Fin 720, columnCertificate j.val) (s : Fin 2) :
    cosetMatrix s * basisMatrix = basisMatrix * actionMatrix s := by
  rw [← packed_cosetMatrix, ← packed_basisMatrix, ← packed_actionMatrix]
  apply Packed.matrix_mul_eq
  · exact originalColumns_length s
  · decide +kernel
  · intro j
    simpa only [Array.getElem!_toList] using (h j).2 s

private theorem bit_of_shift_zero (v m r : ℕ) (h : v >>> m = 0) (hm : m ≤ r) : bit v r = 0 := by
  have hb := congrArg (fun x => bit x (r - m)) h
  simpa only [bit, Nat.testBit_shiftRight, Nat.add_sub_of_le hm, Nat.zero_testBit,
    Bool.false_eq_true, ↓reduceIte] using hb

private theorem bit_slice (v m n r : ℕ) (hr : r < n) :
    bit ((v >>> m) % 2 ^ n) r = bit v (m + r) := by
  simp [bit, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, hr]

private theorem cut_order : ∀ t u : Factor, t.val ≤ u.val → cut t.val ≤ cut u.val := by
  decide +kernel

private theorem cut_next_order : ∀ t u : Factor, t.val < u.val → cut (t.val + 1) ≤ cut u.val := by
  decide +kernel

private theorem column_in_block_before (m : ℕ) (hm : m ≤ 33) (j : Fin 720)
    (hj : j.val < cut m) :
    ∃ t : Factor, cut t.val ≤ j.val ∧ j.val < cut (t.val + 1) := by
  induction m with
  | zero => rw [cut_zero] at hj; omega
  | succ m ih =>
    by_cases h : j.val < cut m
    · exact ih (by omega) h
    · refine ⟨⟨m, by omega⟩, ?_, hj⟩
      change cut m ≤ j.val
      omega

private theorem column_in_block (j : Fin 720) :
    ∃ t : Factor, cut t.val ≤ j.val ∧ j.val < cut (t.val + 1) :=
  column_in_block_before 33 (by omega) j (by rw [cut_last]; exact j.isLt)

theorem upper_of_blocks (h : ∀ t : Factor, blockCertificate t)
    (t : Factor) (s : Fin 2) (x y : Fin 720)
    (hx : cut t.val ≤ x.val) (hy : y.val < cut t.val) : actionMatrix s x y = 0 := by
  obtain ⟨u, hu, hu'⟩ := column_in_block y
  have hut : u.val < t.val := by
    by_contra hn
    have := cut_order t u (by omega)
    omega
  have hd := (cut_step u).1
  let z : Fin (degree u) := ⟨y.val - cut u.val, by omega⟩
  have hz : cut u.val + z.val = y.val := by dsimp [z]; omega
  have hc := (h u s z).1
  rw [hz] at hc
  exact bit_of_shift_zero _ _ _ hc ((cut_next_order u t hut).trans hx)

theorem diagonal_of_blocks (h : ∀ t : Factor, blockCertificate t)
    (t : Factor) (s : Fin 2) (x y : Fin (degree t)) :
    actionMatrix s (blockIndex t x) (blockIndex t y) = factorMatrix t s x y := by
  change bit (Witness.adaptedColumns[s.val]!)[cut t.val + y.val]! (cut t.val + x.val) = _
  rw [← bit_slice _ _ (degree t) _ x.isLt, (h t s y).2]
  rfl
end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
