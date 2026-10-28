module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Data
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Binary column arithmetic for the M₁₁ factor certificates

Packed natural numbers encode columns, with the least significant bit first.
XOR and selection of columns decode to addition and matrix multiplication.
The concrete consumers certify low-rank operators and cyclic bases for the
three nontrivial eleven-coset factors. No computation oracle is used.
Source context: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity
open Matrix

abbrev bit (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

theorem bit_xor (x y j : ℕ) : bit (x ^^^ y) j = bit x j + bit y j := by
  simp only [bit, Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

def xorList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x ^^^ xorList xs

theorem bit_xorList (xs : List ℕ) (j : ℕ) :
    bit (xorList xs) j = (xs.map (fun x => bit x j)).sum := by
  induction xs with
  | nil => simp [xorList, bit]
  | cons x xs ih => simp only [xorList, bit_xor, List.map_cons, List.sum_cons, ih]

def vector {n : ℕ} (x : ℕ) : Fin n → ZMod 2 := fun i => bit x i.val

def matrix {m n : ℕ} (a : Fin n → ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bit (a j) i.val

def act {n : ℕ} (a : Fin n → ℕ) (x : ℕ) : ℕ :=
  xorList (List.ofFn fun j : Fin n => if x.testBit j.val then a j else 0)

def product {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) : Fin n → ℕ :=
  fun j => act a (b j)

def plus {n : ℕ} (a b : Fin n → ℕ) : Fin n → ℕ := fun j => a j ^^^ b j

def identity (n : ℕ) : Fin n → ℕ := fun i => 2 ^ i.val

theorem vector_xor {n : ℕ} (x y : ℕ) :
    vector (n := n) (x ^^^ y) = vector x + vector y := by
  funext i
  exact bit_xor x y i.val

theorem vector_zero {n : ℕ} : vector (n := n) 0 = 0 := by
  funext i
  simp [vector, bit]

theorem vector_act {m n : ℕ} (a : Fin n → ℕ) (x : ℕ) :
    vector (n := m) (act a x) = (matrix a).mulVec (vector (n := n) x) := by
  funext i
  simp only [vector, act, bit_xorList, List.map_ofFn, List.sum_ofFn,
    Matrix.mulVec, dotProduct, matrix]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply, bit]
  cases x.testBit j.val <;> simp

theorem matrix_product {m n p : ℕ} (a : Fin n → ℕ) (b : Fin p → ℕ) :
    matrix (m := m) (product a b) = matrix a * matrix (m := n) b := by
  funext i j
  exact congrFun (vector_act (m := m) a (b j)) i

theorem matrix_plus {m n : ℕ} (a b : Fin n → ℕ) :
    matrix (m := m) (plus a b) = matrix a + matrix b := by
  funext i j
  exact bit_xor (a j) (b j) i.val

theorem matrix_identity (n : ℕ) : matrix (m := n) (identity n) = 1 := by
  funext i j
  simp only [matrix, identity, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  by_cases h : j.val = i.val
  · simp [h]
  · simp [h, Ne.symm h]

def outer {n : ℕ} (u r : ℕ) : Fin n → ℕ :=
  fun j => if r.testBit j.val then u else 0

theorem matrix_outer {m n : ℕ} (u r : ℕ) :
    matrix (m := m) (outer (n := n) u r) = vecMulVec (vector u) (vector r) := by
  funext i j
  simp only [matrix, outer, vecMulVec, Matrix.of_apply, vector, bit]
  by_cases h : r.testBit j.val = true <;> simp [h]

theorem product_eq_one {n : ℕ} (a b : Fin n → ℕ)
    (h : product a b = identity n) :
    matrix a * matrix b = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [← matrix_product, h, matrix_identity]

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity
