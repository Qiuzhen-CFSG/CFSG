module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Packed binary matrix certificates for the Co₁ local action

XOR of binary rows decodes as addition over F₂. Thus small natural-number
certificates imply ordinary rectangular matrix multiplication identities.
This is used for the ATLAS `Co1G1-max5W1` words and their invariant subspace;
all numerical certificates are reduced by the Lean kernel.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co1.CentralizerSection.Packed

abbrev bit (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

lemma bit_xor (x y j : ℕ) : bit (x ^^^ y) j = bit x j + bit y j := by
  simp only [bit, Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

def xorList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x ^^^ xorList xs

lemma bit_xorList (xs : List ℕ) (j : ℕ) :
    bit (xorList xs) j = (xs.map (fun x => bit x j)).sum := by
  induction xs with
  | nil => simp [xorList, bit]
  | cons x xs ih =>
    simpa only [xorList, bit_xor, List.map_cons, List.sum_cons] using congrArg (bit x j + ·) ih

def decode {m n : ℕ} (rows : Fin m → ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (rows i) j.val

def product {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) : Fin m → ℕ :=
  fun i => xorList (List.ofFn (fun k : Fin n => if (a i).testBit k.val then b k else 0))

lemma decode_product {m n p : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) :
    (decode (product a b) : Matrix (Fin m) (Fin p) (ZMod 2)) =
      (decode a : Matrix (Fin m) (Fin n) (ZMod 2)) * decode b := by
  funext i j
  simp only [decode, product, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [bit]
  cases h : (a i).testBit k.val <;> simp [h]

lemma mul_eq_of_certificate {m n p : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (c : Fin m → ℕ) (h : product a b = c) :
    (decode a : Matrix (Fin m) (Fin n) (ZMod 2)) * decode b =
      (decode c : Matrix (Fin m) (Fin p) (ZMod 2)) := by
  rw [← decode_product, h]

end Sporadic.LeechRelated.Co1.CentralizerSection.Packed
