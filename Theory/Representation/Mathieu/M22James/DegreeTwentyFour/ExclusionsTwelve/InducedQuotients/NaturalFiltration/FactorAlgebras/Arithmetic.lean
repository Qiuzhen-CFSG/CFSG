module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.Flag
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion

/-!
# Sound packed F₄ matrix arithmetic and orbit certificates

A vector is stored as two binary words, its coefficients of 1 and omega.
XOR implements addition, and multiplication by omega sends (a,b) to
(b,a+b), since omega² = 1+omega. The scalar table, packed products and
outer products are proved to decode to operations in the actual field.
Recursive orbit certificates and inverse matrices then supply the hypotheses
of the field-general rank-one matrix-algebra criterion.

This supports the natural induced Mathieu factors in Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, pp.15–16 and
Theorem 6.6/Table 6.7. The orbit proof adapts the project's binary G₂
`CycleFiltration/FactorAlgebras.lean`; no external code is copied.
-/

@[expose] public section
open Matrix
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.FactorAlgebraCertificate
abbrev Packed := ℕ × ℕ
def value (x : Packed) (j : ℕ) : Field :=
  (if x.1.testBit j then 1 else 0) +
  (if x.2.testBit j then QuadraticAlgebra.omega else 0)
def plus (x y : Packed) : Packed := (x.1 ^^^ y.1, x.2 ^^^ y.2)
def omegaMul (x : Packed) : Packed := (x.2, x.1 ^^^ x.2)
lemma value_zero (j : ℕ) : value (0, 0) j = 0 := by simp [value]
lemma value_plus (x y : Packed) (j : ℕ) : value (plus x y) j = value x j + value y j := by
  simp only [value, plus, Nat.testBit_xor]
  cases x.1.testBit j <;> cases x.2.testBit j <;>
    cases y.1.testBit j <;> cases y.2.testBit j <;> decide
lemma value_omegaMul (x : Packed) (j : ℕ) :
    value (omegaMul x) j = (QuadraticAlgebra.omega : Field) * value x j := by
  have h : ∀ a b : Bool,
      ((if b then 1 else 0) + (if a ^^ b then QuadraticAlgebra.omega else 0) : Field) =
        QuadraticAlgebra.omega * ((if a then 1 else 0) + (if b then QuadraticAlgebra.omega else 0)) := by
    decide +kernel
  dsimp only [value, omegaMul]
  rw [Nat.testBit_xor]
  exact h (x.1.testBit j) (x.2.testBit j)

def total : List Packed → Packed
  | [] => (0, 0)
  | x :: xs => plus x (total xs)
lemma value_total (xs : List Packed) (j : ℕ) :
    value (total xs) j = (xs.map (fun x => value x j)).sum := by
  induction xs with
  | nil => exact value_zero j
  | cons x xs ih => simp only [total, value_plus, ih, List.map_cons, List.sum_cons]

def scale (x : Packed) (k : ℕ) (y : Packed) : Packed :=
  plus (if x.1.testBit k then y else (0, 0))
    (if x.2.testBit k then omegaMul y else (0, 0))
lemma value_scale (x y : Packed) (k j : ℕ) :
    value (scale x k y) j = value x k * value y j := by
  rw [show value x k = (if x.1.testBit k then 1 else 0) +
    (if x.2.testBit k then QuadraticAlgebra.omega else 0) from rfl, add_mul]
  simp only [scale, value_plus]
  cases h : x.1.testBit k <;> cases h' : x.2.testBit k <;>
    simp only [Bool.false_eq_true, ↓reduceIte, value_zero, value_omegaMul,
      zero_mul, one_mul, zero_add, add_zero]

abbrev Rows (n : ℕ) := Fin n → Packed
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) Field
def vector {n : ℕ} (x : Packed) : Fin n → Field := fun i => value x i.val
def matrix {n : ℕ} (xs : Rows n) : Mat n := fun i => vector (xs i)
def rowProduct {n : ℕ} (x : Packed) (ys : Rows n) : Packed :=
  total (List.ofFn fun k : Fin n => scale x k.val (ys k))
def product {n : ℕ} (xs ys : Rows n) : Rows n := fun i => rowProduct (xs i) ys
lemma vector_rowProduct {n : ℕ} (x : Packed) (ys : Rows n) :
    vector (rowProduct x ys) = vecMul (vector x) (matrix ys) := by
  funext j
  simp only [vector, rowProduct, value_total, List.map_ofFn, List.sum_ofFn,
    vecMul, dotProduct, matrix, Function.comp_apply, value_scale]
lemma matrix_product {n : ℕ} (xs ys : Rows n) :
    matrix (product xs ys) = matrix xs * matrix ys := by
  funext i
  exact vector_rowProduct (xs i) ys

def add {n : ℕ} (xs ys : Rows n) : Rows n := fun i => plus (xs i) (ys i)
lemma matrix_add {n : ℕ} (xs ys : Rows n) : matrix (add xs ys) = matrix xs + matrix ys := by
  funext i j
  exact value_plus _ _ _
def identity {n : ℕ} : Rows n := fun i => (2 ^ i.val, 0)
lemma matrix_identity {n : ℕ} : matrix (identity : Rows n) = 1 := by
  funext i j
  simp [matrix, vector, identity, value, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

def rankOneRows {n : ℕ} (u v : Packed) : Rows n := fun i => scale u i.val v
lemma matrix_rankOneRows {n : ℕ} (u v : Packed) :
    matrix (rankOneRows u v : Rows n) = vecMulVec (vector u) (vector v) := by
  funext i j
  exact value_scale _ _ _ _
lemma matrix_mul_mem {n : ℕ} (Q : Subalgebra Field (Mat (n+1))) (x y z : Rows (n+1))
    (hx : matrix x ∈ Q) (hy : matrix y ∈ Q) (h : product x y = z) : matrix z ∈ Q := by
  rw [← h, matrix_product]
  exact Q.mul_mem hx hy
lemma matrix_add_mem {n : ℕ} (Q : Subalgebra Field (Mat (n+1))) (x y : Rows (n+1))
    (hx : matrix x ∈ Q) (hy : matrix y ∈ Q) : matrix (add x y) ∈ Q := by
  rw [matrix_add]
  exact Q.add_mem hx hy

lemma span_rows_of_inverse {n : ℕ} (xs ys : Rows (n+1)) (h : product ys xs = identity) :
    Submodule.span Field (Set.range (matrix xs)) = ⊤ := by
  have hm : matrix ys * matrix xs = 1 := by
    rw [← matrix_product, h, matrix_identity]
  change Submodule.span Field (Set.range (matrix xs).row) = ⊤
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro v
  refine ⟨vecMul v (matrix ys), ?_⟩
  change vecMul (vecMul v (matrix ys)) (matrix xs) = v
  rw [vecMul_vecMul, hm, vecMul_one]


lemma column_realizations {n : ℕ} (Q : Subalgebra Field (Mat (n+1))) (A : Fin 2 → Mat (n+1))
    (hA : ∀ a, A a ∈ Q) (xs : Rows (n+1)) (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, (A (a i)).mulVec (vector (xs (p i))) = vector (xs i.succ)) :
    ∀ i, ∃ L : Mat (n+1), L ∈ Q ∧ L.mulVec (vector (xs 0)) = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨A (a i) * L, Q.mul_mem (hA _) hL, ?_⟩
      rw [← mulVec_mulVec, he, hs i]

lemma row_realizations {n : ℕ} (Q : Subalgebra Field (Mat (n+1))) (A : Fin 2 → Mat (n+1))
    (hA : ∀ a, A a ∈ Q) (xs : Rows (n+1)) (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, vecMul (vector (xs (p i))) (A (a i)) = vector (xs i.succ)) :
    ∀ i, ∃ R : Mat (n+1), R ∈ Q ∧ vecMul (vector (xs 0)) R = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * A (a i), Q.mul_mem hR (hA _), ?_⟩
      rw [← vecMul_vecMul, he, hs i]

lemma full_of_orbits {n : ℕ} (Q : Subalgebra Field (Mat (n+1))) (A : Fin 2 → Mat (n+1))
    (hA : ∀ a, A a ∈ Q) (cols rows ci ri : Rows (n+1))
    (cp rp : Fin n → Fin (n+1)) (ca ra : Fin n → Fin 2)
    (hcp : ∀ i, cp i < i.succ) (hrp : ∀ i, rp i < i.succ)
    (hcs : ∀ i, (A (ca i)).mulVec (vector (cols (cp i))) = vector (cols i.succ))
    (hrs : ∀ i, vecMul (vector (rows (rp i))) (A (ra i)) = vector (rows i.succ))
    (hci : product ci cols = identity) (hri : product ri rows = identity)
    (huv : vecMulVec (vector (cols 0)) (vector (rows 0)) ∈ Q) : Q = ⊤ := by
  classical
  choose L hL heL using column_realizations Q A hA cols cp ca hcp hcs
  choose R hR heR using row_realizations Q A hA rows rp ra hrp hrs
  apply G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one Q (vector (cols 0))
    (vector (rows 0)) L R hL hR huv
  · have he : (fun i => (L i).mulVec (vector (cols 0))) = matrix cols := funext heL
    rw [he]
    exact span_rows_of_inverse cols ci hci
  · have he : (fun i => vecMul (vector (rows 0)) (R i)) = matrix rows := funext heR
    rw [he]
    exact span_rows_of_inverse rows ri hri




end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.FactorAlgebraCertificate
