module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Packed
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Packed coefficient pairing and matrix trace

Coefficientwise multiplication of two rows over F₄ is computed by AND and XOR
of their two bit planes. XOR of the paired rows, followed by summation of the
first `n` bits, gives `trace(A * B)` when the second list encodes `B.transpose`.
The final summation is truncated to `n`, so no assumption about unused high
bits is needed. Bounded chunks permit independent kernel checks of the pairing.

This supplies the semantic bridge for the ATLAS degree-896 HS trace certificate;
source conventions and attribution are in `../../source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace
open Packed

private theorem decode_add (a b : Row) (i : ℕ) :
    decode (Base.addRow a b) i = decode a i + decode b i := Base.entry_add omega a b i

private theorem decode_shift (a : Row) (k i : ℕ) :
    decode (a.1 >>> k, a.2 >>> k) i = decode a (k + i) := by
  simp only [decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_shiftRight]

def mulRow (a b : Row) : Row :=
  ((a.1 &&& b.1) ^^^ (a.2 &&& b.2),
   (a.1 &&& b.2) ^^^ (a.2 &&& b.1) ^^^ (a.2 &&& b.2))

private theorem decode_mulRow (a b : Row) (i : ℕ) :
    decode (mulRow a b) i = decode a i * decode b i := by
  simp only [decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    mulRow, Nat.testBit_xor, Nat.testBit_and]
  cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> decide +kernel

def productsSum : Mat → Mat → Row
  | a :: as, b :: bs => Base.addRow (mulRow a b) (productsSum as bs)
  | _, _ => (0, 0)

theorem decode_productsSum (a c : Mat) (hc : c.length = a.length) (j : ℕ) :
    decode (productsSum a c) j =
      ∑ i : Fin a.length, decode (a.getD i.val (0, 0)) j *
        decode (c.getD i.val (0, 0)) j := by
  induction a generalizing c with
  | nil => simp [productsSum, decode]
  | cons r rs ih =>
    cases c with
    | nil => simp at hc
    | cons t ts =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hc
      rw [productsSum, decode_add, decode_mulRow, ih ts hc]
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
        List.getD_cons_zero, List.getD_cons_succ]

private theorem productsSum_append (a c a' c' : Mat) (hc : c.length = a.length) :
    productsSum (a ++ a') (c ++ c') =
      Base.addRow (productsSum a c) (productsSum a' c') := by
  induction a generalizing c with
  | nil =>
    have : c = [] := List.length_eq_zero_iff.mp hc
    subst c
    simp [productsSum, Base.addRow]
  | cons r rs ih =>
    cases c with
    | nil => simp at hc
    | cons t ts =>
      have ht : ts.length = rs.length := by simpa using hc
      simp only [List.cons_append, productsSum, ih ts ht, Base.addRow, Nat.xor_assoc]

/-- A bounded part of the coefficientwise pairing, with a proposed XOR sum. -/
structure PairChunk where
  left : Mat
  right : Mat
  value : Row

def checkChunks (xs : List PairChunk) : Bool :=
  xs.all fun x => x.right.length == x.left.length && productsSum x.left x.right == x.value

def sumValues : List PairChunk → Row
  | [] => (0, 0)
  | x :: xs => Base.addRow x.value (sumValues xs)

theorem productsSum_chunks (xs : List PairChunk) (h : checkChunks xs = true) :
    productsSum (xs.flatMap PairChunk.left) (xs.flatMap PairChunk.right) = sumValues xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [checkChunks, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.flatMap_cons, productsSum_append _ _ _ _ h.1.1, h.1.2,
      ih h.2, sumValues]

/-- XOR the first `n` entries of a packed row into its low coefficient. -/
def sumRow : ℕ → Row → Row
  | 0, _ => (0, 0)
  | n + 1, a => Base.addRow (a.1 % 2, a.2 % 2) (sumRow n (a.1 / 2, a.2 / 2))

private theorem decode_low (a : Row) : decode (a.1 % 2, a.2 % 2) 0 = decode a 0 := by
  simp only [decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit]
  rw [show (a.1 % 2).testBit 0 = a.1.testBit 0 by simp]
  rw [show (a.2 % 2).testBit 0 = a.2.testBit 0 by simp]

private theorem decode_div (a : Row) (i : ℕ) :
    decode (a.1 / 2, a.2 / 2) i = decode a (i + 1) := by
  simpa only [Nat.shiftRight_one, Nat.add_comm] using decode_shift a 1 i

theorem decode_sumRow (n : ℕ) (a : Row) :
    decode (sumRow n a) 0 = ∑ j ∈ Finset.range n, decode a j := by
  induction n generalizing a with
  | zero => simp [sumRow, decode]
  | succ n ih =>
    rw [sumRow, decode_add, decode_low, ih, Finset.sum_range_succ']
    simp only [decode_div, add_comm]

/-- The packed pairing with the rows of the transposed second matrix is the
ordinary matrix trace. Only entries below `n` are summed. -/
theorem trace_eq_of_transpose (n : ℕ) (a b c : Mat)
    (ha : a.length = n) (hc : c.length = n)
    (ht : eval n c = (eval n b).transpose) :
    (eval n a * eval n b).trace = decode (sumRow n (productsSum a c)) 0 := by
  subst n
  rw [decode_sumRow]
  simp_rw [decode_productsSum a c hc]
  rw [Finset.sum_comm]
  change (∑ i : Fin a.length, ∑ j : Fin a.length,
    decode (a.getD i.val (0, 0)) j.val * decode (b.getD j.val (0, 0)) i.val) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => decode (a.getD i.val (0, 0)) j * decode (c.getD i.val (0, 0)) j)]
  apply Finset.sum_congr rfl
  intro j _
  have hij := congrFun (congrFun ht i) j
  change decode (c.getD i.val (0, 0)) j.val = decode (b.getD j.val (0, 0)) i.val at hij
  rw [hij]

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace
