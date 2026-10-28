module

public import Theory.SpecificGroups.Janko4.Model
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Packed binary matrix multiplication

A row of a product over GF(2) is the XOR of the right-hand rows selected
by the left-hand row. `decode_packedMul` proves this algorithm agrees with
ordinary matrix multiplication. It supplies the kernel-checked arithmetic
interface for the ATLAS J4 generator certificates; no external evaluator
is trusted. See `Model.Data` for the ATLAS source and bit convention.
-/

@[expose] public section

namespace Janko4.GeneratorCertificates
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
  | cons x xs ih => simpa only [xorList, bit_xor, List.map_cons, List.sum_cons] using congrArg (bit x j + ·) ih

def packedRow (x : ℕ) (ys : Vector ℕ 112) : ℕ :=
  xorList (List.ofFn (fun k : Fin 112 => if x.testBit k.val then ys.get k else 0))
def packedMul (xs ys : Vector ℕ 112) : Vector ℕ 112 :=
  Vector.ofFn (fun i => packedRow (xs.get i) ys)
lemma get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt
lemma decode_packedMul (xs ys : Vector ℕ 112) :
    decodeRows (packedMul xs ys) = decodeRows xs * decodeRows ys := by
  funext i j
  simp only [decodeRows, packedMul, get_ofFn]
  change bit (packedRow (xs.get i) ys) j.val = _
  rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [decodeRows, bit]
  cases h : (xs.get i).testBit k.val <;> simp [h]

def packedOne : Vector ℕ 112 := Vector.ofFn (fun i => 2^i.val)
lemma decode_packedOne : decodeRows packedOne = 1 := by
  funext i j
  simp only [decodeRows, packedOne, get_ofFn, Nat.testBit_two_pow, decide_eq_true_eq, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem packedMul_eq_of_rows (xs ys zs : Vector ℕ 112)
    (h : ∀ i : Fin 112, packedRow (xs.get i) ys = zs.get i) :
    packedMul xs ys = zs := by
  apply Vector.ext
  intro i hi
  change (packedMul xs ys).get ⟨i, hi⟩ = zs.get ⟨i, hi⟩
  rw [packedMul, get_ofFn]
  exact h ⟨i, hi⟩

end Janko4.GeneratorCertificates
