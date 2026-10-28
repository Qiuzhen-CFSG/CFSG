module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RowArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.ProjectionApplication
/-!
# Small vector and sum checks for the complementary projections

A packed multiplication by a one-column list computes the binary pairing.
This gives sound checks for a matrix killing the stored column and for the
stored covector killing a matrix. Sequential XOR checks certify the short
algebra sums. The numerical consumers are in `Numerics.lean`.
Source data: `Degree320Pair/source/README.md`.
-/

@[expose] public section
open Thompson.BinaryMatrix Matrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks

def digits (n v : Nat) : List Nat :=
  List.ofFn fun i : Fin n => if v.testBit i.val then 1 else 0

theorem bit_digit (v i : Nat) : bit (if v.testBit i then 1 else 0) 0 = bit v i := by
  cases h : v.testBit i <;> simp [bit, h]

theorem pairing_sound (n v l r : Nat) (h : skipRow l (digits n v) = r) :
    (fun i : Fin n => bit l i.val) ⬝ᵥ (fun i : Fin n => bit v i.val) = bit r 0 := by
  rw [skipRow_eq, shiftRow_eq_row] at h
  rw [← h, digits, bit_row]
  simp only [Nat.zero_add, bit_digit, dotProduct]

theorem mulVec_zero_sound (n : Nat) (a : List Nat) (v : Nat)
    (ha : a.length = n)
    (h : checkRows a (digits n v) (List.replicate n 0) = true) :
    (decode n a.toArray).mulVec (fun i => bit v i.val) = 0 := by
  ext i
  have hh := checkRows_get a (digits n v) (List.replicate n 0) h i.val
    (by simpa only [ha] using i.isLt)
  have hz : (List.replicate n 0)[i.val]! = 0 := by simp
  rw [hz] at hh
  have he := pairing_sound n v a[i.val]! 0 (by simpa only [skipRow_eq] using hh)
  simpa only [mulVec, decode, List.getElem!_toArray, Pi.zero_apply, bit,
    Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte] using he

theorem vecMul_zero_sound (n : Nat) (a : List Nat) (l : Nat)
    (ha : a.length = n) (h : skipRow l a = 0) :
    Matrix.vecMul (fun i => bit l i.val) (decode n a.toArray) = 0 := by
  ext j
  change (∑ i : Fin n, bit l i.val * bit a.toArray[i.val]! j.val) = 0
  rw [← bit_row_array n a.toArray (by simpa using ha)]
  simp only [← shiftRow_eq_row, ← skipRow_eq, h, bit,
    Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks
open Thompson.BinaryMatrix Matrix

def checkAdd : List Nat → List Nat → List Nat → Bool
  | [], [], [] => true
  | a :: as, b :: bs, c :: cs => ((a ^^^ b) == c) && checkAdd as bs cs
  | _, _, _ => false

theorem checkAdd_get (a b c : List Nat) (h : checkAdd a b c = true)
    (i : Nat) (hi : i < a.length) : a[i]! ^^^ b[i]! = c[i]! := by
  induction a generalizing b c i with
  | nil => simp at hi
  | cons x xs ih =>
    cases b with
    | nil => simp [checkAdd] at h
    | cons y ys =>
      cases c with
      | nil => simp [checkAdd] at h
      | cons z zs =>
        simp only [checkAdd, Bool.and_eq_true, beq_iff_eq] at h
        cases i with
        | zero => simpa using h.1
        | succ i => simpa using ih _ _ h.2 i (Nat.lt_of_succ_lt_succ hi)

theorem add_sound (n : Nat) (a b c : List Nat) (ha : a.length = n)
    (h : checkAdd a b c = true) :
    decode n a.toArray + decode n b.toArray = decode n c.toArray := by
  ext i j
  have hh := checkAdd_get a b c h i.val (by simpa only [ha] using i.isLt)
  simpa only [decode, Matrix.add_apply, List.getElem!_toArray, bit_xor] using
    congrArg (fun x => bit x j.val) hh

def identityRows (n : Nat) : List Nat := List.ofFn (fun i : Fin n => 2 ^ i.val)

theorem identity_sound (n : Nat) : decode n (identityRows n).toArray = 1 := by
  ext i j
  simp [decode, identityRows, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

def checkOuter (n v l : Nat) (a : List Nat) : Bool :=
  (List.range n).all fun i => a[i]! == if v.testBit i then l else 0

theorem outer_sound (n v l : Nat) (a : List Nat) (h : checkOuter n v l a = true) :
    decode n a.toArray = Matrix.vecMulVec (fun i => bit v i.val) (fun i => bit l i.val) := by
  ext i j
  have hh : a[i.val]! = if v.testBit i.val then l else 0 :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simp only [decode, List.getElem!_toArray, hh, Matrix.vecMulVec_apply, bit]
  cases hv : v.testBit i.val <;> simp [Nat.zero_testBit]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneChecks
