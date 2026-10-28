module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic.Ring

/-!
Two bit planes encode a row over F₄. A set bit in the first plane contributes
1, and a set bit in the second contributes t, where t²=t+1. XOR is addition;
multiplication by t sends (a,b) to (b,a+b). The row-product checker selects
rows in these two ways. Its soundness proof works over every characteristic-two
field and does not trust the program that proposes the matrix products.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed

abbrev Row := ℕ × ℕ
abbrev Mat := Array Row

def addRow (a b : Row) : Row := (a.1 ^^^ b.1, a.2 ^^^ b.2)
def timesT (a : Row) : Row := (a.2, a.1 ^^^ a.2)
def rowProduct (a : Row) (b : Mat) : ℕ → Row
  | 0 => (0, 0)
  | k + 1 => addRow (rowProduct a b k)
      (addRow (if a.1.testBit k then b[k]! else (0, 0))
        (if a.2.testBit k then timesT b[k]! else (0, 0)))

def checkProduct (n : ℕ) (a b c : Mat) : Bool :=
  (List.range n).all fun i => rowProduct a[i]! b n == c[i]!
def checkInverse (n : ℕ) (a b : Mat) : Bool :=
  (List.range n).all fun i => rowProduct a[i]! b n == (2 ^ i, 0)

variable {F : Type*} [Field F] [CharP F 2]

def bit (a j : ℕ) : F := if a.testBit j then 1 else 0
def entry (t : F) (a : Row) (j : ℕ) : F := bit a.1 j + t * bit a.2 j
def eval (t : F) (n : ℕ) (a : Mat) : Matrix (Fin n) (Fin n) F :=
  fun i j => entry t a[i.val]! j.val

theorem bit_xor (a b j : ℕ) : bit (F := F) (a ^^^ b) j = bit a j + bit b j := by
  simp only [bit, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> simp [CharTwo.add_self_eq_zero]

omit [CharP F 2] in
@[simp] theorem entry_zero (t : F) (j : ℕ) : entry t (0, 0) j = 0 := by
  simp [entry, bit]

theorem entry_add (t : F) (a b : Row) (j : ℕ) :
    entry t (addRow a b) j = entry t a j + entry t b j := by
  simp only [entry, addRow, bit_xor]
  ring

theorem entry_timesT (t : F) (ht : t ^ 2 = t + 1) (a : Row) (j : ℕ) :
    entry t (timesT a) j = t * entry t a j := by
  simp only [entry, timesT, bit_xor]
  calc
    _ = t * bit a.1 j + (t + 1) * bit a.2 j := by ring
    _ = _ := by rw [← ht]; ring

theorem entry_rowProduct (t : F) (ht : t ^ 2 = t + 1) (a : Row) (b : Mat)
    (n j : ℕ) :
    entry t (rowProduct a b n) j =
      ∑ k ∈ Finset.range n, entry t a k * entry t b[k]! j := by
  induction n with
  | zero => simp [rowProduct]
  | succ n ih =>
    rw [rowProduct, entry_add, ih, Finset.sum_range_succ]
    congr 1
    rw [entry_add]
    have h0 : entry t (if a.1.testBit n then b[n]! else (0, 0)) j =
        bit a.1 n * entry t b[n]! j := by
      cases h : a.1.testBit n <;> simp [h, bit]
    have h1 : entry t (if a.2.testBit n then timesT b[n]! else (0, 0)) j =
        (t * bit a.2 n) * entry t b[n]! j := by
      cases h : a.2.testBit n <;> simp [h, bit, entry_timesT t ht]
    rw [h0, h1, ← add_mul]
    rfl

theorem eval_product (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (a b c : Mat)
    (h : checkProduct n a b c = true) : eval t n a * eval t n b = eval t n c := by
  ext i j
  have hi : rowProduct a[i.val]! b n = c[i.val]! :=
    eq_of_beq (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change (∑ k : Fin n, entry t a[i.val]! k.val * entry t b[k.val]! j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => entry t a[i.val]! k * entry t b[k]! j.val),
    ← entry_rowProduct t ht, hi]
  rfl

theorem eval_inverse (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (a b : Mat)
    (h : checkInverse n a b = true) : eval t n a * eval t n b = 1 := by
  ext i j
  have hi : rowProduct a[i.val]! b n = (2 ^ i.val, 0) :=
    eq_of_beq (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change (∑ k : Fin n, entry t a[i.val]! k.val * entry t b[k.val]! j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => entry t a[i.val]! k * entry t b[k]! j.val),
    ← entry_rowProduct t ht, hi]
  simp [entry, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem eval_frobenius (t : F) (n : ℕ) (a : Mat) :
    eval (t ^ 2) n a = (eval t n a).map (frobenius F 2) := by
  ext i j
  change entry (t ^ 2) a[i.val]! j.val = (entry t a[i.val]! j.val) ^ 2
  simp only [entry, add_pow_char, mul_pow, bit]
  split_ifs <;> simp

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed
