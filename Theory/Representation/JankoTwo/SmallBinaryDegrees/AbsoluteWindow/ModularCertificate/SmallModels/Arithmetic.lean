module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-!
# Checked arithmetic for the Hall--Janko matrices over four elements

The codes 0,1,2,3 denote 0,1,t,t+1 with t²=t+1. Addition and multiplication
are finite tables whose evaluations are proved correct in every characteristic-two
field, in every universe. Matrix, vector, outer-product and trace identities
transport through this evaluation. The Boolean equality checkers are proved
sound and may be closed by kernel reduction on literal data.

Coefficient Frobenius is also proved explicitly. Thus changing t to t² really
applies the field Frobenius to every matrix entry. This module introduces no
trusted computation primitive or finite-field assumption.

Source encoding: ATLAS J2G1-f4r6aB0 and J2G1-f4r14aB0; see ../Source.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
namespace Arithmetic

def coefficient {F : Type*} [Field F] (t : F) : Fin 4 → F := ![0, 1, t, t + 1]
def addCode : Fin 4 → Fin 4 → Fin 4 :=
  !![0, 1, 2, 3; 1, 0, 3, 2; 2, 3, 0, 1; 3, 2, 1, 0]
def mulCode : Fin 4 → Fin 4 → Fin 4 :=
  !![0, 0, 0, 0; 0, 1, 2, 3; 0, 2, 3, 1; 0, 3, 1, 2]

variable {F : Type*} [Field F] [CharP F 2]

theorem coefficient_add (t : F) (a b : Fin 4) :
    coefficient t (addCode a b) = coefficient t a + coefficient t b := by
  fin_cases a <;> fin_cases b <;>
    simp [coefficient, addCode, CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals reduce_mod_char!

theorem coefficient_mul (t : F) (ht : t ^ 2 = t + 1) (a b : Fin 4) :
    coefficient t (mulCode a b) = coefficient t a * coefficient t b := by
  fin_cases a <;> fin_cases b
  · change (0) = (0) * (0)
    ring_nf
  · change (0) = (0) * (1)
    ring_nf
  · change (0) = (0) * (t)
    ring_nf
  · change (0) = (0) * (t + 1)
    ring_nf
  · change (0) = (1) * (0)
    ring_nf
  · change (1) = (1) * (1)
    ring_nf
  · change (t) = (1) * (t)
    ring_nf
  · change (t + 1) = (1) * (t + 1)
    ring_nf
  · change (0) = (t) * (0)
    ring_nf
  · change (t) = (t) * (1)
    ring_nf
  · change (t + 1) = (t) * (t)
    ring_nf
    rw [ht]
    ring_nf
  · change (1) = (t) * (t + 1)
    ring_nf
    rw [ht]
    ring_nf
    reduce_mod_char!
  · change (0) = (t + 1) * (0)
    ring_nf
  · change (t + 1) = (t + 1) * (1)
    ring_nf
  · change (1) = (t + 1) * (t)
    ring_nf
    rw [ht]
    ring_nf
    reduce_mod_char!
  · change (t) = (t + 1) * (t + 1)
    ring_nf
    rw [ht]
    ring_nf
    reduce_mod_char!

theorem coefficient_frobenius (t : F) (a : Fin 4) :
    coefficient (t ^ 2) a = (coefficient t a) ^ 2 := by
  fin_cases a <;> simp [coefficient, add_pow_char]

def codeSum : List (Fin 4) → Fin 4
  | [] => 0
  | a :: as => addCode a (codeSum as)

abbrev CodeMatrix (n : ℕ) := Matrix (Fin n) (Fin n) (Fin 4)
abbrev CodeVector (n : ℕ) := Fin n → Fin 4

variable {n : ℕ}

def codeProduct (M N : CodeMatrix n) : CodeMatrix n :=
  fun i j => codeSum (List.ofFn (fun k => mulCode (M i k) (N k j)))
def codeMulVec (M : CodeMatrix n) (x : CodeVector n) : CodeVector n :=
  fun i => codeSum (List.ofFn (fun k => mulCode (M i k) (x k)))
def codeVecMul (x : CodeVector n) (M : CodeMatrix n) : CodeVector n :=
  fun j => codeSum (List.ofFn (fun k => mulCode (x k) (M k j)))
def evalMatrix (t : F) (M : CodeMatrix n) : Matrix (Fin n) (Fin n) F :=
  M.map (coefficient t)
def evalVector (t : F) (x : CodeVector n) : Fin n → F := coefficient t ∘ x

theorem coefficient_sum (t : F) (xs : List (Fin 4)) :
    coefficient t (codeSum xs) = (xs.map (coefficient t)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [codeSum, coefficient_add, ih, List.map_cons, List.sum_cons]

theorem eval_product (t : F) (ht : t ^ 2 = t + 1) (M N : CodeMatrix n) :
    evalMatrix t (codeProduct M N) = evalMatrix t M * evalMatrix t N := by
  ext i j
  change coefficient t (codeSum (List.ofFn (fun k => mulCode (M i k) (N k j)))) =
    ∑ k, coefficient t (M i k) * coefficient t (N k j)
  rw [coefficient_sum, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun k _ => coefficient_mul t ht _ _

theorem eval_mulVec (t : F) (ht : t ^ 2 = t + 1) (M : CodeMatrix n) (x : CodeVector n) :
    evalVector t (codeMulVec M x) = (evalMatrix t M).mulVec (evalVector t x) := by
  funext i
  change coefficient t (codeSum (List.ofFn (fun k => mulCode (M i k) (x k)))) =
    ∑ k, coefficient t (M i k) * coefficient t (x k)
  rw [coefficient_sum, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun k _ => coefficient_mul t ht _ _

theorem eval_vecMul (t : F) (ht : t ^ 2 = t + 1) (x : CodeVector n) (M : CodeMatrix n) :
    evalVector t (codeVecMul x M) = Matrix.vecMul (evalVector t x) (evalMatrix t M) := by
  funext j
  change coefficient t (codeSum (List.ofFn (fun k => mulCode (x k) (M k j)))) =
    ∑ k, coefficient t (x k) * coefficient t (M k j)
  rw [coefficient_sum, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun k _ => coefficient_mul t ht _ _

def codeOne : CodeMatrix n := fun i j => if i = j then 1 else 0
def codeZero : CodeMatrix n := fun _ _ => 0
def codeAdd (M N : CodeMatrix n) : CodeMatrix n := fun i j => addCode (M i j) (N i j)
def codeScale (c : Fin 4) (M : CodeMatrix n) : CodeMatrix n := fun i j => mulCode c (M i j)
def codeOuter (x y : CodeVector n) : CodeMatrix n := fun i j => mulCode (x i) (y j)
def codeTrace (M : CodeMatrix n) : Fin 4 := codeSum (List.ofFn fun i => M i i)

omit [CharP F 2] in
theorem eval_one (t : F) : evalMatrix t (codeOne : CodeMatrix n) = 1 := by
  ext i j
  change coefficient t (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> rfl

omit [CharP F 2] in
theorem eval_zero (t : F) : evalMatrix t (codeZero : CodeMatrix n) = 0 := rfl

theorem eval_add (t : F) (M N : CodeMatrix n) :
    evalMatrix t (codeAdd M N) = evalMatrix t M + evalMatrix t N := by
  ext i j
  exact coefficient_add t _ _

theorem eval_scale (t : F) (ht : t ^ 2 = t + 1) (c : Fin 4) (M : CodeMatrix n) :
    evalMatrix t (codeScale c M) = coefficient t c • evalMatrix t M := by
  ext i j
  exact coefficient_mul t ht _ _

theorem eval_outer (t : F) (ht : t ^ 2 = t + 1) (x y : CodeVector n) :
    evalMatrix t (codeOuter x y) = Matrix.vecMulVec (evalVector t x) (evalVector t y) := by
  ext i j
  exact coefficient_mul t ht _ _

theorem eval_trace (t : F) (M : CodeMatrix n) :
    coefficient t (codeTrace M) = (evalMatrix t M).trace := by
  rw [codeTrace, coefficient_sum, List.map_ofFn, List.sum_ofFn]
  rfl

theorem eval_frobenius (t : F) (M : CodeMatrix n) :
    evalMatrix (t ^ 2) M = (evalMatrix t M).map (frobenius F 2) := by
  ext i j
  exact coefficient_frobenius t (M i j)

def checkMatrix (M N : CodeMatrix n) : Bool :=
  (List.finRange n).all (fun i => (List.finRange n).all
    (fun j => (M i j).val == (N i j).val))

theorem checkMatrix_sound (M N : CodeMatrix n) (h : checkMatrix M N = true) : M = N := by
  funext i j
  apply Fin.ext
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j))

def checkVector (x y : CodeVector n) : Bool :=
  (List.finRange n).all (fun i => (x i).val == (y i).val)

theorem checkVector_sound (x y : CodeVector n) (h : checkVector x y = true) : x = y := by
  funext i
  apply Fin.ext
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

end Arithmetic
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
