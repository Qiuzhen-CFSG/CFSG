module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Data
public import Mathlib.Data.Nat.Bits
/-!
# Packing the literal pivot minor

Column zero selects ambient column 538; all other columns select i + 540.
Thus a packed minor row is obtained by shifting away 541 bits and prefixing
bit 538. The bit lemma below identifies this operation with the actual
`pivotMinor`, and `product_one_row` applies the soundness theorem of
`RowArithmetic` to the supplied inverse. No inverse property is assumed.

Source: the fixed `Binary/source/section1000.json`, derived from the ATLAS
HS exterior-square section. Attribution and rights: `Binary/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Rank
open scoped BigOperators
open Thompson.BinaryMatrix
open RowArithmetic
def pack (x : ℕ) : ℕ := Nat.bit (x.testBit 538) (x >>> 541)
theorem bit_pack_nat (x j : ℕ) :
    bit (pack x) j = bit x (if j = 0 then 538 else j + 540) := by
  unfold bit pack
  cases j with
  | zero => simp
  | succ k => simp [Nat.testBit_bit_succ, Nat.testBit_shiftRight, Nat.add_assoc,
      Nat.add_comm]

theorem bit_pack (x : ℕ) (j : Fin 1000) :
    bit (pack x) j.val = bit x (pivotColumn j).val := bit_pack_nat x j.val

theorem minor_row (i : Fin 1000) :
    pivotMinor i = vector 1000 (pack liftRows[i.val]!) := by
  funext j
  change bit liftRows.toList[i.val]! (pivotColumn j).val = _
  rw [Array.getElem!_toList]
  exact (bit_pack _ j).symm

theorem product_one_row (i : Fin 1000)
    (h : combine pivotInverseRows.toList (pack liftRows[i.val]!) = 2 ^ i.val) :
    (pivotMinor * pivotInverse) i = (1 : Matrix (Fin 1000) (Fin 1000) (ZMod 2)) i := by
  have hv := vector_combine pivotInverseRows.toList 1000 1000
    (by decide +kernel) (pack liftRows[i.val]!)
  rw [matrix_toList, h] at hv
  calc
    _ = Matrix.vecMul (vector 1000 (pack liftRows[i.val]!)) pivotInverse :=
      congrArg (fun row => Matrix.vecMul row pivotInverse) (minor_row i)
    _ = vector 1000 (2 ^ i.val) := hv.symm
    _ = (1 : Matrix (Fin 1000) (Fin 1000) (ZMod 2)) i := by
      funext j
      simp [vector, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Rank
