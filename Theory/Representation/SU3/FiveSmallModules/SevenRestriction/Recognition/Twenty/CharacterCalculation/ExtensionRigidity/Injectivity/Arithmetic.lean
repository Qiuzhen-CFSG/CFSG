module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.CharP.Two
public import Theory.LinearAlgebra.PackedBinaryRows

/-!
# Soundness of packed degree-twenty Bruhat equations

A packed row is a linear form in the 400 entries of an arbitrary matrix over
any field of characteristic two. XOR adds these forms. The tensor-row lemma
identifies a packed coefficient row with the corresponding entry of A X B;
a checked inverse therefore proves injectivity over the original field.

Source of the application: the SU Bruhat equations from Huppert II.10.12,
proved in ExtensionRigidity.Averaging. All finite computations are separate
from these general soundness proofs.
-/

@[expose] public section

open scoped BigOperators Matrix
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.Certificate
variable {K : Type*} [Field K] [CharP K 2]

def entry (a j : Nat) : K := if a.testBit j then 1 else 0
def matrix (a : Fin 20 → Nat) : Matrix (Fin 20) (Fin 20) K :=
  Matrix.of fun i j => entry (a i) j.val
def evaluate (X : Matrix (Fin 20) (Fin 20) K) (a : Nat) : K :=
  ∑ r, ∑ c, entry a (20 * r.val + c.val) * X r c

theorem entry_xor (a b j : Nat) :
    (entry (a ^^^ b) j : K) = entry a j + entry b j := by
  simp only [entry, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> simp [CharTwo.add_self_eq_zero]

theorem evaluate_xor (X : Matrix (Fin 20) (Fin 20) K) (a b : Nat) :
    evaluate X (a ^^^ b) = evaluate X a + evaluate X b := by
  simp only [evaluate, entry_xor, add_mul, Finset.sum_add_distrib]

omit [CharP K 2] in
theorem evaluate_zero (X : Matrix (Fin 20) (Fin 20) K) : evaluate X 0 = 0 := by
  simp [evaluate, entry]

omit [CharP K 2] in
theorem evaluate_single (X : Matrix (Fin 20) (Fin 20) K) (r c : Fin 20) :
    evaluate X (2 ^ (20 * r.val + c.val)) = X r c := by
  have he (u v : Fin 20) : 20 * r.val + c.val = 20 * u.val + v.val ↔ u = r ∧ v = c := by
    constructor
    · intro h
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp [evaluate, entry, Nat.testBit_two_pow, he, ite_and]

def xorList : List Nat → Nat
  | [] => 0
  | a :: as => a ^^^ xorList as

theorem evaluate_xorList (X : Matrix (Fin 20) (Fin 20) K) (as : List Nat) :
    evaluate X (xorList as) = (as.map (evaluate X)).sum := by
  induction as with
  | nil => exact evaluate_zero X
  | cons a as ih => simp only [xorList, evaluate_xor, ih, List.map_cons, List.sum_cons]

def tensorRow (A B : Fin 20 → Nat) (r c : Fin 20) : Nat :=
  xorList (List.ofFn fun i : Fin 20 => xorList (List.ofFn fun j : Fin 20 =>
    if (A r).testBit i.val && (B j).testBit c.val then 2 ^ (20 * i.val + j.val) else 0))

theorem evaluate_tensorRow (X : Matrix (Fin 20) (Fin 20) K)
    (A B : Fin 20 → Nat) (r c : Fin 20) :
    evaluate X (tensorRow A B r c) = (matrix (K := K) A * X * matrix (K := K) B : Matrix (Fin 20) (Fin 20) K) r c := by
  simp only [tensorRow, evaluate_xorList, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  have term (i j : Fin 20) :
      evaluate X (if (A r).testBit i.val && (B j).testBit c.val then
        2 ^ (20 * i.val + j.val) else 0) =
      matrix (K := K) A r i * X i j * matrix (K := K) B j c := by
    cases hA : (A r).testBit i.val <;> cases hB : (B j).testBit c.val <;>
      simp [hA, hB, evaluate_zero, evaluate_single, matrix, entry]
  simp_rw [term]
  change (∑ i, ∑ j, matrix (K := K) A r i * X i j * matrix (K := K) B j c) =
    ∑ j, (∑ i, matrix (K := K) A r i * X i j) * matrix (K := K) B j c
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

omit [CharP K 2] in
theorem evaluate_sub (X Y : Matrix (Fin 20) (Fin 20) K) (a : Nat) :
    evaluate (X - Y) a = evaluate X a - evaluate Y a := by
  simp [evaluate, mul_sub, Finset.sum_sub_distrib]

theorem evaluate_listProduct_eq_zero (X : Matrix (Fin 20) (Fin 20) K)
    (a start : Nat) (rows : List Nat) (h : ∀ r ∈ rows, evaluate X r = 0) :
    evaluate X (PackedBinaryRows.listProduct a start rows) = 0 := by
  induction rows generalizing start with
  | nil => exact evaluate_zero X
  | cons r rows ih =>
    rw [PackedBinaryRows.listProduct, evaluate_xor,
      ih (start + 1) (fun s hs => h s (List.mem_cons_of_mem r hs)), add_zero]
    split
    · exact h r (List.mem_cons_self)
    · exact evaluate_zero X

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.Certificate
