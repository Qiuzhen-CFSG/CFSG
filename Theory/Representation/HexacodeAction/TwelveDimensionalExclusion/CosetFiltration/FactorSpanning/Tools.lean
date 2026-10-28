module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Interface
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion
import Mathlib.Algebra.BigOperators.Fin

/-!
# Small arithmetic certificates for the central coset factors

Four-element lookup tables are proved to evaluate in the fixed hexacode field.
Thus kernel checks of code products certify actual matrix products without
repeatedly reducing the quadratic-field implementation. Recursive column and
row orbits and two inverse checks feed the existing rank-one density criterion.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
The concrete licensed ATLAS witnesses are supplied in the sibling certificates;
this module contains their arithmetic and linear-algebra justification.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.Spanning
open Matrix

abbrev Code := Fin 4
abbrev Codes (n : ℕ) := Fin n → Code
abbrev MatCodes (n : ℕ) := Fin n → Codes n

def addCode : Code → Code → Code :=
  ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]]
def mulCode : Code → Code → Code :=
  ![![0,0,0,0], ![0,1,2,3], ![0,2,3,1], ![0,3,1,2]]

theorem entry_add : ∀ a b, entry (addCode a b) = entry a + entry b := by decide +kernel
theorem entry_mul : ∀ a b, entry (mulCode a b) = entry a * entry b := by decide +kernel

def sumCode : List Code → Code
  | [] => 0
  | x :: xs => addCode x (sumCode xs)

theorem entry_sum (xs : List Code) : entry (sumCode xs) = (xs.map entry).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumCode, entry_add, List.map_cons, List.sum_cons, ih]

def vector {n : ℕ} (v : Codes n) : Fin n → F := fun i => entry (v i)
def matrix {n : ℕ} (A : MatCodes n) : Matrix (Fin n) (Fin n) F := fun i => vector (A i)
def dot {n : ℕ} (v w : Codes n) : Code :=
  sumCode (List.ofFn fun i => mulCode (v i) (w i))
def product {n : ℕ} (A B : MatCodes n) : MatCodes n :=
  fun i j => dot (A i) (fun k => B k j)
def columnProduct {n : ℕ} (A : MatCodes n) (v : Codes n) : Codes n :=
  fun i => dot (A i) v
def rowProduct {n : ℕ} (v : Codes n) (A : MatCodes n) : Codes n :=
  fun j => dot v (fun i => A i j)
def identity (n : ℕ) : MatCodes n := fun i j => if i = j then 1 else 0
def plus {n : ℕ} (A B : MatCodes n) : MatCodes n :=
  fun i j => addCode (A i j) (B i j)
def scalar (n : ℕ) (c : Code) : MatCodes n := fun i j => if i = j then c else 0
def rankOne {n : ℕ} (u v : Codes n) : MatCodes n := fun i j => mulCode (u i) (v j)

theorem entry_dot {n : ℕ} (v w : Codes n) :
    entry (dot v w) = dotProduct (vector v) (vector w) := by
  simp only [dot, entry_sum, List.map_ofFn, List.sum_ofFn, Function.comp_apply, entry_mul, dotProduct, vector]
theorem matrix_product {n : ℕ} (A B : MatCodes n) :
    matrix (product A B) = matrix A * matrix B := by
  funext i j
  exact entry_dot _ _
theorem vector_columnProduct {n : ℕ} (A : MatCodes n) (v : Codes n) :
    vector (columnProduct A v) = (matrix A).mulVec (vector v) := by
  funext i
  exact entry_dot _ _
theorem vector_rowProduct {n : ℕ} (v : Codes n) (A : MatCodes n) :
    vector (rowProduct v A) = vecMul (vector v) (matrix A) := by
  funext i
  exact entry_dot _ _
theorem matrix_identity (n : ℕ) : matrix (identity n) = 1 := by
  funext i j
  by_cases h : i = j <;> simp [matrix, vector, identity, h, entry, Matrix.one_apply]
theorem matrix_plus {n : ℕ} (A B : MatCodes n) :
    matrix (plus A B) = matrix A + matrix B := by
  funext i j
  exact entry_add _ _
theorem matrix_scalar (n : ℕ) (c : Code) : matrix (scalar n c) = entry c • 1 := by
  funext i j
  by_cases h : i = j <;> simp [matrix, vector, scalar, h, entry]
theorem matrix_rankOne {n : ℕ} (u v : Codes n) :
    matrix (rankOne u v) = vecMulVec (vector u) (vector v) := by
  funext i j
  exact entry_mul _ _

theorem product_mem {n : ℕ} (Q : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (A B C : MatCodes n) (hA : matrix A ∈ Q) (hB : matrix B ∈ Q)
    (h : product A B = C) : matrix C ∈ Q := by
  rw [← h, matrix_product]
  exact Q.mul_mem hA hB

theorem plus_scalar_mem {n : ℕ} (Q : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (A : MatCodes n) (c : Code) (hA : matrix A ∈ Q) :
    matrix (plus A (scalar n c)) ∈ Q := by
  rw [matrix_plus, matrix_scalar]
  exact Q.add_mem hA (Q.smul_mem Q.one_mem _)

theorem span_rows_of_inverse {n : ℕ} (A B : MatCodes n)
    (h : product B A = identity n) : Submodule.span F (Set.range (matrix A)) = ⊤ := by
  have hm : matrix B * matrix A = 1 := by rw [← matrix_product, h, matrix_identity]
  change Submodule.span F (Set.range (matrix A).row) = ⊤
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro v
  refine ⟨vecMul v (matrix B), ?_⟩
  change vecMul (vecMul v (matrix B)) (matrix A) = v
  rw [vecMul_vecMul, hm, vecMul_one]


private theorem column_realizations {n : ℕ}
    (Q : Subalgebra F (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A : Fin 2 → MatCodes (n + 1)) (hA : ∀ a, matrix (A a) ∈ Q)
    (xs : MatCodes (n + 1)) (p : Fin n → Fin (n + 1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, columnProduct (A (a i)) (xs (p i)) = xs i.succ) :
    ∀ i, ∃ L : Matrix (Fin (n + 1)) (Fin (n + 1)) F,
      L ∈ Q ∧ L.mulVec (vector (xs 0)) = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨matrix (A (a i)) * L, Q.mul_mem (hA _) hL, ?_⟩
      rw [← mulVec_mulVec, he, ← vector_columnProduct, hs i]

private theorem row_realizations {n : ℕ}
    (Q : Subalgebra F (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A : Fin 2 → MatCodes (n + 1)) (hA : ∀ a, matrix (A a) ∈ Q)
    (xs : MatCodes (n + 1)) (p : Fin n → Fin (n + 1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, rowProduct (xs (p i)) (A (a i)) = xs i.succ) :
    ∀ i, ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) F,
      R ∈ Q ∧ vecMul (vector (xs 0)) R = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * matrix (A (a i)), Q.mul_mem hR (hA _), ?_⟩
      rw [← vecMul_vecMul, he, ← vector_rowProduct, hs i]

/-- Checked orbit recursions and inverse matrices turn one rank-one element
into the full algebra. The rows of `cols` store the column vectors. -/
theorem full_of_orbits {n : ℕ}
    (Q : Subalgebra F (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A : Fin 2 → MatCodes (n + 1)) (hA : ∀ a, matrix (A a) ∈ Q)
    (cols rows ci ri : MatCodes (n + 1))
    (cp rp : Fin n → Fin (n + 1)) (ca ra : Fin n → Fin 2)
    (hcp : ∀ i, cp i < i.succ) (hrp : ∀ i, rp i < i.succ)
    (hcs : ∀ i, columnProduct (A (ca i)) (cols (cp i)) = cols i.succ)
    (hrs : ∀ i, rowProduct (rows (rp i)) (A (ra i)) = rows i.succ)
    (hci : product ci cols = identity (n + 1))
    (hri : product ri rows = identity (n + 1))
    (huv : matrix (rankOne (cols 0) (rows 0)) ∈ Q) : Q = ⊤ := by
  classical
  choose L hL heL using column_realizations Q A hA cols cp ca hcp hcs
  choose R hR heR using row_realizations Q A hA rows rp ra hrp hrs
  rw [matrix_rankOne] at huv
  apply G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one
    Q (vector (cols 0)) (vector (rows 0)) L R hL hR huv
  · have he : (fun i => (L i).mulVec (vector (cols 0))) = matrix cols := funext heL
    rw [he]
    exact span_rows_of_inverse cols ci hci
  · have he : (fun i => vecMul (vector (rows 0)) (R i)) = matrix rows := funext heR
    rw [he]
    exact span_rows_of_inverse rows ri hri

end Representation.Hexacode.TwelveDimensional.CosetCertificate.Spanning
