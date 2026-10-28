module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Transversal

/-!
# Saved M23 matrices as exact native correction blocks

The kernel checks all 460 packed columns. Each is the ten-bit point
correction column, shifted to its destination block. The decoding lemma
then proves every matrix entry and the sparse multiplication formula.
The local cocode equivalence is not assumed by these finite identities.

Source application: Guralnick--Malle I, Proposition 5.1, M23 paragraph;
data and conventions in `source/README.md`.
-/

namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
@[expose] public noncomputable section

/-- Every saved column has precisely the block given by the native correction. -/
theorem saved_columns (k : Fin 2) (i : Fin 23) (y : Fin 10) :
    generatorColumns k (finProdFinEquiv (i,y)) =
      quotientMask (correctionPoint k i (quotientPoint y)) <<< (10 * (blockPerm k i).val) := by
  revert k i y
  decide +kernel

theorem quotientMask_bound (x : Fin 23) : quotientMask x < 2^10 := by
  revert x
  decide +kernel

private theorem bit_block (n : ℕ) (hn : n < 2^10) (i j : Fin 23) (x : Fin 10) :
    bit (n <<< (10*j.val)) (x.val + 10*i.val) =
      if i = j then bit n x.val else 0 := by
  by_cases h : i = j
  · subst j
    simp only [bit, Nat.testBit_shiftLeft]
    have hle : 10*i.val ≤ x.val + 10*i.val := by omega
    simp only [hle, decide_true, Bool.true_and]
    simp only [Nat.add_sub_cancel_right, ite_true]
  · rw [if_neg h]
    unfold bit
    rw [Nat.testBit_shiftLeft]
    by_cases hle : 10*j.val ≤ x.val + 10*i.val
    · simp only [hle, decide_true, Bool.true_and]
      have hij : i.val ≠ j.val := fun he => h (Fin.ext he)
      have hb : n < 2^(x.val + 10*i.val - 10*j.val) :=
        hn.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hb]
      rfl
    · simp only [hle, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- The full matrices are the literal sparse native block matrices. -/
theorem saved_matrix (k : Fin 2) (i j : Fin 23) (x y : Fin 10) :
    generatorMatrix k (finProdFinEquiv (i,x)) (finProdFinEquiv (j,y)) =
      if i = blockPerm k j then pointMatrix (correction k j) x y else 0 := by
  change bit (generatorColumns k (finProdFinEquiv (j,y))) (x.val + 10*i.val) = _
  rw [saved_columns, bit_block _ (quotientMask_bound _)]
  simp only [pointMatrix, correction_apply]

/-- The saved generator acts on block i through the actual point correction. -/
theorem saved_mulVec (k : Fin 2) (v : Space) (i : Fin 23) (x : Fin 10) :
    (generatorMatrix k).mulVec v (finProdFinEquiv (blockPerm k i,x)) =
      (pointMatrix (correction k i)).mulVec (fun y => v (finProdFinEquiv (i,y))) x := by
  change (∑ q, generatorMatrix k (finProdFinEquiv (blockPerm k i,x)) q * v q) = _
  rw [← (finProdFinEquiv (m := 23) (n := 10)).sum_comp]
  simp only [Fintype.sum_prod_type, saved_matrix, (blockPerm k).injective.eq_iff]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

end
end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
