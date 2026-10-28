module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Assembly
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA.Blocks
/-!
# Packing the literal first tensor generator

`tensorRow` places the degree-56 row in exactly those 56-bit blocks selected
by the degree-20 row. Induction proves its bit formula. The checked alignment
then identifies every supplied packed row with this construction, so decoding
the shared list is exactly `ambientA`, in the original tensor coordinates.
This is the semantic bridge needed by the numerical section certificates.

Source: R. A. Wilson et al., ATLAS HSG1-f2r20B0 and HSG1-f2r56B0;
`Binary/source/README.md` retains the collective attribution and rights.
The original proof is Apache-2.0.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA
open Thompson.BinaryMatrix

def tensorRow (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k+1, x, y => (if x.testBit 0 then y else 0) ||| (tensorRow n k (x >>> 1) y <<< n)

theorem tensorRow_bit (n m x y i j : ℕ) (hy : y < 2 ^ n) (hi : i < m) (hj : j < n) :
    (tensorRow n m x y).testBit (n*i+j) = (x.testBit i && y.testBit j) := by
  induction m generalizing x i with
  | zero => omega
  | succ m ih =>
    rw [tensorRow, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add]
      have h : ¬ j ≥ n := by omega
      simp only [h, decide_false, Bool.false_and, Bool.or_false]
      cases x.testBit 0 <;> simp
    | succ i =>
      have hge : n * (i+1) + j ≥ n := by simp only [Nat.mul_add, Nat.mul_one]; omega
      have hsub : n * (i+1) + j - n = n*i+j := by simp only [Nat.mul_add, Nat.mul_one]; omega
      have hz : y.testBit (n*(i+1)+j) = false := by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hge)
      have hl : (if x.testBit 0 then y else 0).testBit (n*(i+1)+j) = false := by
        cases x.testBit 0 <;> simp [hz]
      rw [hl]
      simp only [hge, decide_true, Bool.true_and, Bool.false_or, hsub]
      rw [ih (x >>> 1) i (by omega), Nat.testBit_shiftRight]
      rw [Nat.add_comm 1]

theorem tensorRow_entry (n m x y i j : ℕ) (hy : y < 2 ^ n) (hi : i < m) (hj : j < n) :
    bit (tensorRow n m x y) (n*i+j) = bit x i * bit y j := by
  simp only [bit, tensorRow_bit n m x y i j hy hi hj]
  cases x.testBit i <;> cases y.testBit j <;> decide

def ambientPacked : List ℕ := List.ofFn fun i : Fin (20*56) =>
  tensorRow 56 20 Sporadic.LeechRelated.HS.Twenty.aRows[i.divNat.val]!
    D56.aRows[i.modNat.val]!

private theorem a56_bounded : ∀ i : Fin 56, D56.aRows[i.val]! < 2^56 := by decide +kernel

theorem ambientPacked_matrix : RowArithmetic.matrix 1120 1120 ambientPacked = ambientA := by
  rw [show ambientA = tensorMatrix (decode 20 Sporadic.LeechRelated.HS.Twenty.aRows)
      (decode 56 D56.aRows) from rfl]
  funext (i : Fin (20*56)) (j : Fin (20*56))
  rw [tensorMatrix_apply]
  simp only [RowArithmetic.matrix, decode]
  have he : ambientPacked[i.val]! = tensorRow 56 20
      Sporadic.LeechRelated.HS.Twenty.aRows[i.divNat.val]! D56.aRows[i.modNat.val]! := by
    simp only [ambientPacked, List.getElem!_eq_getElem?_getD, List.getElem?_ofFn,
      dif_pos i.isLt, Option.getD_some]
  rw [he]
  have hj : 56*j.divNat.val+j.modNat.val = j.val := Nat.div_add_mod _ _
  conv_lhs => rw [← hj]
  exact tensorRow_entry 56 20 _ _ _ _ (a56_bounded i.modNat) j.divNat.isLt j.modNat.isLt

theorem ambientAligned : Blocks.ambientSuffix0 = ambientPacked := by decide +kernel

theorem ambient_matrix : RowArithmetic.matrix 1120 1120 Blocks.ambientSuffix0 = ambientA := by
  rw [ambientAligned, ambientPacked_matrix]

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA
