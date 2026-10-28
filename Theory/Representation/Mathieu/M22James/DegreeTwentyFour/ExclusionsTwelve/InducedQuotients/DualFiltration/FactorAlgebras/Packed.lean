module
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Data
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion
import Mathlib.Algebra.BigOperators.Fin

/-!
# Packed F₄ certificates for the dual induced factor algebras

Two natural-number masks encode the coefficients of 1 and omega. XOR and
mask exchange implement field addition and multiplication, and are proved to
decode to the ordinary matrix operations. Orbit recurrences construct words
in the generators; checked inverse matrices prove that their images span.
The rank-one matrix criterion then gives the full matrix algebra.

The consumers are the literal factors of dimensions 45, 6 and 15 in
`DualFiltration.Data`. Source context: Guralnick–Malle, Classification of
2F-modules I, Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7.
-/

@[expose] public section
open Matrix
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FactorAlgebras
abbrev Word := Nat × Nat

def decode (x : Word) (i : Nat) : F :=
  ⟨if x.1.testBit i then 1 else 0, if x.2.testBit i then 1 else 0⟩
def add (x y : Word) : Word := (x.1 ^^^ y.1, x.2 ^^^ y.2)
def omega (x : Word) : Word := (x.2, x.1 ^^^ x.2)
def scale (r w : Bool) (x : Word) : Word :=
  add (if r then x else (0, 0)) (if w then omega x else (0, 0))
def sum : List Word → Word
  | [] => (0, 0)
  | x :: xs => add x (sum xs)

theorem decode_zero (i : Nat) : decode (0, 0) i = 0 := by simp [decode]; rfl

theorem decode_add (x y : Word) (i : Nat) :
    decode (add x y) i = decode x i + decode y i := by
  simp only [decode, add, Nat.testBit_xor]
  cases x.1.testBit i <;> cases x.2.testBit i <;>
    cases y.1.testBit i <;> cases y.2.testBit i <;> decide +kernel

theorem decode_omega (x : Word) (i : Nat) :
    decode (omega x) i = (QuadraticAlgebra.omega : F) * decode x i := by
  simp only [decode, omega, Nat.testBit_xor]
  have h : ∀ r w : Bool, (⟨if w then 1 else 0, if r ^^ w then 1 else 0⟩ : F) =
      (QuadraticAlgebra.omega : F) * (⟨if r then 1 else 0, if w then 1 else 0⟩ : F) := by
    decide +kernel
  exact h _ _

theorem decode_scale (r w : Bool) (x : Word) (i : Nat) :
    decode (scale r w x) i = (⟨if r then 1 else 0, if w then 1 else 0⟩ : F) * decode x i := by
  cases r <;> cases w <;> simp only [scale, Bool.false_eq_true, ↓reduceIte,
    decode_add, decode_zero, decode_omega, zero_add, add_zero]
  · exact (zero_mul _).symm
  · rfl
  · exact (one_mul _).symm
  · change _ = ((1 : F) + QuadraticAlgebra.omega) * _
    rw [add_mul, one_mul]

theorem decode_sum (xs : List Word) (i : Nat) :
    decode (sum xs) i = (xs.map (fun x => decode x i)).sum := by
  induction xs with
  | nil => exact decode_zero i
  | cons x xs ih => simp only [sum, decode_add, List.map_cons, List.sum_cons, ih]

def vector {n : Nat} (x : Word) : Fin n → F := fun i => decode x i.val
/-- Packed columns, as in the published factor data. -/
def matrix {m n : Nat} (xs : Fin n → Word) : Matrix (Fin m) (Fin n) F :=
  fun i j => decode (xs j) i.val

def act {n : Nat} (a : Fin n → Word) (x : Word) : Word :=
  sum (List.ofFn fun j : Fin n => scale (x.1.testBit j.val) (x.2.testBit j.val) (a j))
def product {m n : Nat} (a : Fin m → Word) (b : Fin n → Word) : Fin n → Word :=
  fun j => act a (b j)

theorem vector_act {m n : Nat} (a : Fin n → Word) (x : Word) :
    vector (n := m) (act a x) = (matrix a).mulVec (vector (n := n) x) := by
  funext i
  change decode (act a x) i.val = _
  rw [act, decode_sum, List.map_ofFn, List.sum_ofFn]
  change _ = ∑ j : Fin n, decode (a j) i.val * decode x j.val
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply]
  rw [decode_scale]
  exact mul_comm (decode x j.val) (decode (a j) i.val)

theorem matrix_product {m n p : Nat} (a : Fin n → Word) (b : Fin p → Word) :
    matrix (m := m) (product a b) = matrix a * matrix (m := n) b := by
  funext i j
  exact congrFun (vector_act (m := m) a (b j)) i

def identity (n : Nat) : Fin n → Word := fun i => (2 ^ i.val, 0)
theorem matrix_identity (n : Nat) : matrix (m := n) (identity n) = 1 := by
  funext i j
  simp only [matrix, identity, decode, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  by_cases h : j.val = i.val
  · simp [h]; rfl
  · simp [h, Ne.symm h]; rfl

def pack (n : Nat) (b : Fin n → Bool) : Nat := (List.ofFn b).foldr Nat.bit 0
theorem testBit_pack {n : Nat} (b : Fin n → Bool) (i : Fin n) :
    (pack n b).testBit i.val = b i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pack, List.ofFn_succ]
    · simpa only [pack, List.ofFn_succ, List.foldr_cons, Fin.val_succ,
        Nat.testBit_bit_succ] using ih (fun j => b j.succ) j

def split (n x : Nat) : Word :=
  (pack n (fun i => x.testBit (2*i.val)), pack n (fun i => x.testBit (2*i.val+1)))
theorem decode_split {n : Nat} (x : Nat) (i : Fin n) :
    decode (split n x) i.val = entry x i.val := by
  simp only [decode, split, testBit_pack, entry]
theorem matrix_split {m n : Nat} (a : Fin n → Nat) :
    matrix (m := m) (fun j => split m (a j)) = columns a := by
  funext i j
  exact decode_split (a j) i

/-- Entrywise addition on packed matrices. -/
def plus {n : Nat} (a b : Fin n → Word) : Fin n → Word := fun j => add (a j) (b j)
def scaled {n : Nat} (c : Nat) (a : Fin n → Word) : Fin n → Word :=
  fun j => scale (c.testBit 0) (c.testBit 1) (a j)
def scalar (c : Nat) : F := ⟨if c.testBit 0 then 1 else 0, if c.testBit 1 then 1 else 0⟩
theorem matrix_plus {m n : Nat} (a b : Fin n → Word) :
    matrix (m := m) (plus a b) = matrix a + matrix b := by
  funext i j
  exact decode_add (a j) (b j) i.val
theorem matrix_scaled {m n : Nat} (c : Nat) (a : Fin n → Word) :
    matrix (m := m) (scaled c a) = scalar c • matrix a := by
  funext i j
  exact decode_scale _ _ _ _
def step {n : Nat} (t x : Fin n → Word) (c : Nat) : Fin n → Word :=
  plus (product t x) (scaled c (identity n))
theorem matrix_step {n : Nat} (t x : Fin n → Word) (c : Nat) :
    matrix (m := n) (step t x c) = matrix t * matrix x + scalar c • 1 := by
  rw [step, matrix_plus, matrix_product, matrix_scaled, matrix_identity]
theorem step_mem {n : Nat} (Q : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (t x y : Fin n → Word) (c : Nat) (ht : matrix t ∈ Q) (hx : matrix x ∈ Q)
    (h : ∀ j, step t x c j = y j) : matrix y ∈ Q := by
  rw [← funext h, matrix_step]
  exact Q.add_mem (Q.mul_mem ht hx) (Q.smul_mem Q.one_mem _)

def transpose {m n : Nat} (a : Fin n → Word) : Fin m → Word := fun j =>
  (pack n (fun i => (a i).1.testBit j.val), pack n (fun i => (a i).2.testBit j.val))
theorem matrix_transpose {m n : Nat} (a : Fin n → Word) :
    matrix (m := n) (transpose (m := m) a) = (matrix a)ᵀ := by
  funext i j
  simp only [matrix, transpose, decode, testBit_pack, Matrix.transpose_apply]

def outer {n : Nat} (u v : Word) : Fin n → Word :=
  fun j => scale (v.1.testBit j.val) (v.2.testBit j.val) u
theorem matrix_outer {m n : Nat} (u v : Word) :
    matrix (m := m) (outer (n := n) u v) = vecMulVec (vector u) (vector v) := by
  funext i j
  change decode (scale _ _ u) i.val = decode u i.val * decode v j.val
  rw [decode_scale]
  exact mul_comm (decode v j.val) (decode u i.val)

theorem span_of_inverse {n : Nat} (a b : Fin n → Word)
    (h : ∀ j, product a b j = identity n j) :
    Submodule.span F (Set.range (fun j => vector (n := n) (a j))) = ⊤ := by
  have hm : matrix a * matrix b = (1 : Matrix (Fin n) (Fin n) F) := by
    rw [← matrix_product, funext h, matrix_identity]
  change Submodule.span F (Set.range (matrix (m := n) a).col) = ⊤
  rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
  intro v
  refine ⟨(matrix b).mulVec v, ?_⟩
  change (matrix a).mulVec ((matrix b).mulVec v) = v
  rw [mulVec_mulVec, hm, one_mulVec]

theorem column_realizations {n : Nat}
    (Q : Subalgebra F (Matrix (Fin (n+1)) (Fin (n+1)) F))
    (A : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) F)
    (hA : ∀ a, A a ∈ Q) (xs : Fin (n+1) → Word)
    (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, (A (a i)).mulVec (vector (xs (p i))) = vector (xs i.succ)) :
    ∀ i, ∃ L : Matrix (Fin (n+1)) (Fin (n+1)) F,
      L ∈ Q ∧ L.mulVec (vector (xs 0)) = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨A (a i) * L, Q.mul_mem (hA _) hL, ?_⟩
      rw [← mulVec_mulVec, he, hs i]

theorem row_realizations {n : Nat}
    (Q : Subalgebra F (Matrix (Fin (n+1)) (Fin (n+1)) F))
    (A : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) F)
    (hA : ∀ a, A a ∈ Q) (xs : Fin (n+1) → Word)
    (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, vecMul (vector (xs (p i))) (A (a i)) = vector (xs i.succ)) :
    ∀ i, ∃ R : Matrix (Fin (n+1)) (Fin (n+1)) F,
      R ∈ Q ∧ vecMul (vector (xs 0)) R = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * A (a i), Q.mul_mem hR (hA _), ?_⟩
      rw [← vecMul_vecMul, he, hs i]

/-- The saved inverse matrices have the orbit vectors as columns on both sides. -/
theorem full_of_orbits {n : Nat}
    (Q : Subalgebra F (Matrix (Fin (n+1)) (Fin (n+1)) F))
    (A AT : Fin 2 → Fin (n+1) → Word)
    (hA : ∀ a, matrix (A a) ∈ Q)
    (hAT : ∀ a, matrix (m := n+1) (AT a) = (matrix (A a))ᵀ)
    (cols rows ci ri : Fin (n+1) → Word)
    (cp rp : Fin n → Fin (n+1)) (ca ra : Fin n → Fin 2)
    (hcp : ∀ i, cp i < i.succ) (hrp : ∀ i, rp i < i.succ)
    (hcs : ∀ i, act (A (ca i)) (cols (cp i)) = cols i.succ)
    (hrs : ∀ i, act (AT (ra i)) (rows (rp i)) = rows i.succ)
    (hci : ∀ j, product cols ci j = identity (n+1) j)
    (hri : ∀ j, product rows ri j = identity (n+1) j)
    (huv : vecMulVec (vector (cols 0)) (vector (rows 0)) ∈ Q) : Q = ⊤ := by
  classical
  have hcs' i : (matrix (m := n+1) (A (ca i))).mulVec (vector (cols (cp i))) =
      vector (cols i.succ) := by rw [← vector_act, hcs]
  have hrs' i : vecMul (vector (rows (rp i))) (matrix (m := n+1) (A (ra i))) =
      vector (rows i.succ) := by rw [← mulVec_transpose, ← hAT, ← vector_act, hrs]
  choose L hL heL using column_realizations Q (fun a => matrix (A a)) hA cols cp ca hcp hcs'
  choose R hR heR using row_realizations Q (fun a => matrix (A a)) hA rows rp ra hrp hrs'
  apply G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one Q
    (vector (cols 0)) (vector (rows 0)) L R hL hR huv
  · rw [show (fun i => (L i).mulVec (vector (cols 0))) =
      (fun i => vector (cols i)) from funext heL]
    exact span_of_inverse cols ci hci
  · rw [show (fun i => vecMul (vector (rows 0)) (R i)) =
      (fun i => vector (rows i)) from funext heR]
    exact span_of_inverse rows ri hri

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FactorAlgebras
