module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Arithmetic
import Mathlib.Data.List.GetD

/-!
# Packed dot products by binary folding

Pointwise multiplication is implemented by AND and XOR on the coefficient
planes. Ten doubling folds sum 1024 coordinates, with a mask restricting the
sum to the first 896. The soundness theorem identifies the result with the
ordinary field-valued dot product. This avoids 896 scalar row selections for
each null-column check.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
open Packed
open scoped BigOperators

/-- Coefficientwise product of two packed rows over F₄. -/
def pointwise (a b : Row) : Row :=
  ((a.1 &&& b.1) ^^^ (a.2 &&& b.2),
    (a.1 &&& b.2) ^^^ (a.2 &&& b.1) ^^^ (a.2 &&& b.2))

theorem decode_pointwise (a b : Row) (i : ℕ) :
    decode (pointwise a b) i = decode a i * decode b i := by
  simp only [pointwise, decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_xor, Nat.testBit_and]
  cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> decide +kernel

def shift (a : Row) (k : ℕ) : Row := (a.1 >>> k, a.2 >>> k)

theorem decode_shift (a : Row) (k i : ℕ) : decode (shift a k) i = decode a (i + k) := by
  simp only [shift, decode, Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_shiftRight, Nat.add_comm]

/-- Fold successive blocks of lengths 1, 2, 4, ... using characteristic two. -/
def fold : ℕ → Row → Row
  | 0, a => a
  | k + 1, a => fold k (Base.addRow a (shift a (2 ^ k)))

theorem decode_fold (k : ℕ) (a : Row) (j : ℕ) :
    decode (fold k a) j = ∑ i ∈ Finset.range (2 ^ k), decode a (j + i) := by
  induction k generalizing a with
  | zero => simp [fold]
  | succ k ih =>
    rw [fold, ih]
    simp only [decode_add, decode_shift, Finset.sum_add_distrib]
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega

/-- Mask off the coordinates outside the desired dimension. -/
def mask (n : ℕ) (a : Row) : Row := (a.1 &&& (2 ^ n - 1), a.2 &&& (2 ^ n - 1))

theorem decode_mask (n : ℕ) (a : Row) (i : ℕ) :
    decode (mask n a) i = if i < n then decode a i else 0 := by
  by_cases h : i < n <;>
    simp [mask, decode, Base.entry,
      Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
      h]

/-- The two low bits after folding represent a finite field dot product. -/
def dot (k n : ℕ) (a b : Row) : Four := decode (fold k (mask n (pointwise a b))) 0

theorem dot_eq (k n : ℕ) (h : n ≤ 2 ^ k) (a b : Row) :
    dot k n a b = ∑ i : Fin n, decode a i.val * decode b i.val := by
  rw [dot, decode_fold]
  simp only [Nat.zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun i => decode a i * decode b i)]
  calc
    _ = ∑ i ∈ Finset.range n, decode (mask n (pointwise a b)) i := by
      symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro i _ hi
      have hn : ¬i < n := by simpa only [Finset.mem_range] using hi
      simp only [decode_mask, if_neg hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [decode_mask, if_pos (Finset.mem_range.mp hi), decode_pointwise]

/-- Check a list of null-vector equations using the folded dot product. -/
def checkDots (k n : ℕ) (b : Row) (a : Mat) : Bool :=
  a.all fun r => decide (dot k n r b = 0)

theorem checkDots_get (k n : ℕ) (b : Row) (a : Mat)
    (h : checkDots k n b a = true) (i : ℕ) (hi : i < a.length) :
    dot k n (a.getD i (0, 0)) b = 0 := by
  apply of_decide_eq_true
  apply List.all_eq_true.mp h
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem checkDots_split (k n : ℕ) (b : Row) (a : Mat) (m : ℕ)
    (h₁ : checkDots k n b (a.take m) = true)
    (h₂ : checkDots k n b (a.drop m) = true) : checkDots k n b a = true := by
  have h : checkDots k n b (a.take m ++ a.drop m) = true := by
    simp only [checkDots, List.all_append, Bool.and_eq_true] at *
    exact ⟨h₁, h₂⟩
  simpa only [List.take_append_drop] using h

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
