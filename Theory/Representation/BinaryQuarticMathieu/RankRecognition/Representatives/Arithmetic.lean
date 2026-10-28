module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Data
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Exact ranks from reversible packed row operations

XOR of packed binary rows is proved to decode as addition over F₂. Matrix
products therefore admit small kernel-checked word certificates. If row
operations and their reverses relate a matrix to E, and E both factors through
and maps onto the rank-r diagonal matrix, the ordinary matrix rank is r.
The standard basis and its dual identify this rank with the actual contraction
image dimension. No algorithmic rank value is assumed.

The XOR multiplication proof follows the elementary implementation in
`Theory/SpecificGroups/Janko4/Model/GeneratorCertificates/Packed.lean`, specialized
here without importing any group model.
-/

@[expose] public section
namespace BinaryQuarticMathieu.RankRecognition.Representatives
abbrev Rows := Fin 10 → Nat
abbrev bit (x j : Nat) : F := if x.testBit j then 1 else 0
lemma bit_xor (x y j : Nat) : bit (x ^^^ y) j = bit x j + bit y j := by
  simp only [bit, Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

def xorList : List Nat → Nat
  | [] => 0
  | x :: xs => x ^^^ xorList xs
lemma bit_xorList (xs : List Nat) (j : Nat) :
    bit (xorList xs) j = (xs.map (fun x => bit x j)).sum := by
  induction xs with
  | nil => simp [xorList, bit]
  | cons x xs ih =>
    simpa only [xorList, bit_xor, List.map_cons, List.sum_cons] using congrArg (bit x j + ·) ih

def rowProduct (x : Nat) (ys : Rows) : Nat :=
  xorList (List.ofFn (fun k : Fin 10 => if x.testBit k.val then ys k else 0))
def matrix (xs : Rows) : Matrix (Fin 10) (Fin 10) F := fun i j => bit (xs i) j.val

def product (xs ys : Rows) : Rows := fun i => rowProduct (xs i) ys
lemma matrix_product (xs ys : Rows) : matrix (product xs ys) = matrix xs * matrix ys := by
  funext i j
  change bit (rowProduct (xs i) ys) j.val = _
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [matrix, bit]
  cases h : (xs i).testBit k.val <;> simp [h]

lemma contractionRank_eq_rank (Q : Form) (v w : U) :
    contractionRank Q v w = (contractionMatrix Q v w).rank := by
  have hm : LinearMap.toMatrix (Pi.basisFun F (Fin 10)) (Pi.basisFun F (Fin 10)).dualBasis
      (contraction Q v w) = contractionMatrix Q v w := by
    ext j i
    simp [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr, Pi.basisFun_apply,
      contractionMatrix, basisVector]
  rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun F (Fin 10)).dualBasis
    (Pi.basisFun F (Fin 10)), ← hm, Matrix.toLin_toMatrix]
  rfl

lemma rank_eq_of_reversible_rows (M E L S : Rows) (hL : product L M = E)
    (hS : product S E = M) : (matrix M).rank = (matrix E).rank := by
  apply le_antisymm
  · have he := congrArg matrix hS
    rw [matrix_product] at he
    rw [← he]
    exact Matrix.rank_mul_le_right _ _
  · have he := congrArg matrix hL
    rw [matrix_product] at he
    rw [← he]
    exact Matrix.rank_mul_le_right _ _

def diagonalRows (r : Fin 11) : Rows := fun i => if i.val < r.val then 2 ^ i.val else 0

lemma matrix_diagonalRows (r : Fin 11) :
    matrix (diagonalRows r) = Matrix.diagonal (fun i : Fin 10 => if i.val < r.val then (1 : F) else 0) := by
  ext i j
  simp only [matrix, diagonalRows, bit, Matrix.diagonal_apply]
  by_cases hi : i.val < r.val
  · simp [hi, Nat.testBit_two_pow, Fin.ext_iff]
  · simp [hi]

lemma rank_diagonalRows (r : Fin 11) : (matrix (diagonalRows r)).rank = r.val := by
  rw [matrix_diagonalRows, Matrix.rank_diagonal]
  have hc : ∀ r : Fin 11, (Finset.univ.filter (fun i : Fin 10 => i.val < r.val)).card = r.val := by
    decide +kernel
  have he : ∀ i : Fin 10, (if i.val < r.val then (1 : F) else 0) ≠ 0 ↔ i.val < r.val := by
    intro i
    split_ifs <;> simp_all
  simpa only [Fintype.card_subtype, he] using hc r

lemma rank_eq_of_certificate (M E L S B : Rows) (r : Fin 11)
    (hL : product L M = E) (hS : product S E = M)
    (hu : product (diagonalRows r) E = E) (hl : product E B = diagonalRows r) :
    (matrix M).rank = r.val := by
  rw [rank_eq_of_reversible_rows M E L S hL hS, ← rank_diagonalRows r]
  apply le_antisymm
  · have he := congrArg matrix hu
    rw [matrix_product] at he
    rw [← he]
    exact Matrix.rank_mul_le_left _ _
  · have he := congrArg matrix hl
    rw [matrix_product] at he
    rw [← he]
    exact Matrix.rank_mul_le_left _ _

end BinaryQuarticMathieu.RankRecognition.Representatives
