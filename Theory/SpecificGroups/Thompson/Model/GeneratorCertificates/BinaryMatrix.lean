module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Packed binary matrix certificates

A natural number represents a binary row, with bit `j` giving entry `j`.
Multiplication selects rows of the right matrix and adds them by XOR. The
soundness theorem follows by induction on the number of selected rows and
identifies this computation with the usual matrix product over `ZMod 2`.
This is the arithmetic checker for the ATLAS Thompson generator certificates.
-/

open scoped BigOperators
namespace Thompson.BinaryMatrix

@[expose] public def bit (a j : ℕ) : ZMod 2 := if a.testBit j then 1 else 0

public theorem bit_xor (a b j : ℕ) : bit (a ^^^ b) j = bit a j + bit b j := by
  simp only [bit, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

@[expose] public def rowProduct (a : ℕ) (b : Array ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => rowProduct a b k ^^^ (if a.testBit k then b[k]! else 0)

public theorem bit_rowProduct (a : ℕ) (b : Array ℕ) (n j : ℕ) :
    bit (rowProduct a b n) j = ∑ k ∈ Finset.range n, bit a k * bit b[k]! j := by
  induction n with
  | zero => simp [rowProduct, bit]
  | succ n ih =>
    rw [rowProduct, bit_xor, ih, Finset.sum_range_succ]
    congr 1
    cases h : a.testBit n <;> simp [bit, h]


@[expose] public def decode (n : ℕ) (a : Array ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => bit a[i.val]! j.val

public theorem decode_mul (n : ℕ) (a b c : Array ℕ)
    (h : ∀ i : Fin n, rowProduct a[i.val]! b n = c[i.val]!) :
    decode n a * decode n b = decode n c := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = bit c[i.val]! j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit a[i.val]! k * bit b[k]! j.val), ← bit_rowProduct, h i]

public theorem decode_mul_one (n : ℕ) (a b : Array ℕ)
    (h : ∀ i : Fin n, rowProduct a[i.val]! b n = 2 ^ i.val) :
    decode n a * decode n b = 1 := by
  ext i j
  change (∑ k : Fin n, bit a[i.val]! k.val * bit b[k.val]! j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => bit a[i.val]! k * bit b[k]! j.val), ← bit_rowProduct, h i]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

end Thompson.BinaryMatrix
