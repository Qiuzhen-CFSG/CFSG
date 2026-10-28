module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.MatrixChecks
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion

/-!
# Packed certificates for full binary matrix algebras

A checked rank-one element and two checked orbit bases imply density. Products
are checked by recursive XOR on stored rows, using the decoding theorem from
`MatrixChecks`. This is the finite linear algebra used for the Hermitian M22
factors in Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate
open MatrixChecks
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) (ZMod 2)
def entry (l : List ℕ) (i : ℕ) : ℕ := l[i]?.getD 0
def vector {n : ℕ} (x : ℕ) : Fin n → ZMod 2 := fun i => bit x i.val
def matrix {n : ℕ} (l : List ℕ) : Mat n := fun i => vector (entry l i.val)

theorem factorMatrix_entry_shift (i : Fin 2) (t : Factor) (j : Fin 2)
    (x y : Fin (degree i t)) :
    bit (actionColumns i j (blockIndex i t y) >>> cut i t.val) x.val =
      factorMatrix i t j x y := by
  simp only [bit, Nat.testBit_shiftRight, factorMatrix, actionMatrix, blockIndex]
  rfl

theorem vector_combine {n : ℕ} (l : List ℕ) (hl : l.length = n) (x : ℕ) :
    vector (n := n) (combineList l x) = vecMul (vector x) (matrix l) := by
  funext j
  rw [vector, bit_combineList l n hl]
  simp only [vecMul, dotProduct, matrix, vector, entry, mul_comm]

theorem matrix_product {n : ℕ} (xs ys zs : List ℕ) (hy : ys.length = n)
    (h : ∀ i : Fin n, combineList ys (entry xs i.val) = entry zs i.val) :
    matrix (n := n) xs * matrix ys = matrix zs := by
  funext i
  exact (vector_combine ys hy _).symm.trans (congrArg vector (h i))

theorem mul_mem {n : ℕ} (Q : Subalgebra (ZMod 2) (Mat n))
    (xs ys zs : List ℕ) (hx : matrix xs ∈ Q) (hy : matrix ys ∈ Q)
    (hlen : ys.length = n)
    (h : ∀ i : Fin n, combineList ys (entry xs i.val) = entry zs i.val) :
    matrix zs ∈ Q := by
  rw [← matrix_product xs ys zs hlen h]
  exact Q.mul_mem hx hy

theorem add_mem {n : ℕ} (Q : Subalgebra (ZMod 2) (Mat n))
    (xs ys zs : List ℕ) (hx : matrix xs ∈ Q) (hy : matrix ys ∈ Q)
    (h : ∀ i : Fin n, entry xs i.val ^^^ entry ys i.val = entry zs i.val) :
    matrix zs ∈ Q := by
  have he : matrix (n := n) xs + matrix ys = matrix zs := by
    ext i j
    exact (bit_xor _ _ _).symm.trans (congrArg (fun x => bit x j.val) (h i))
  rw [← he]
  exact Q.add_mem hx hy

theorem one_mem {n : ℕ} (Q : Subalgebra (ZMod 2) (Mat n)) (xs : List ℕ)
    (h : ∀ i : Fin n, entry xs i.val = 2 ^ i.val) : matrix xs ∈ Q := by
  have he : matrix (n := n) xs = 1 := by
    ext i j
    simp only [matrix, vector, h i, bit_power, Matrix.one_apply, Fin.val_inj]
  rw [he]
  exact Q.one_mem

theorem rankOne_eq {n : ℕ} (xs : List ℕ) (u v : ℕ)
    (h : ∀ i : Fin n, entry xs i.val = if u.testBit i.val then v else 0) :
    matrix (n := n) xs = vecMulVec (vector u) (vector v) := by
  ext i j
  simp only [matrix, vector, h i, vecMulVec_apply, bit]
  cases u.testBit i.val <;> simp

theorem span_rows_of_inverse {n : ℕ} (xs ys : List ℕ) (hx : xs.length = n)
    (h : ∀ i : Fin n, combineList xs (entry ys i.val) = 2 ^ i.val) :
    Submodule.span (ZMod 2) (Set.range (matrix (n := n) xs)) = ⊤ := by
  have hm : matrix (n := n) ys * matrix xs = 1 := by
    ext i j
    have he := congrArg (fun v => v j) (vector_combine xs hx (entry ys i.val))
    rw [h i] at he
    simpa only [vector, bit_power, Fin.val_inj, Matrix.one_apply, Matrix.mul_apply, vecMul, dotProduct, matrix, vector] using he.symm
  change Submodule.span (ZMod 2) (Set.range (matrix xs).row) = ⊤
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro v
  refine ⟨vecMul v (matrix ys), ?_⟩
  change vecMul (vecMul v (matrix ys)) (matrix xs) = v
  rw [vecMul_vecMul, hm, vecMul_one]

private theorem column_realizations {m : ℕ} (Q : Subalgebra (ZMod 2) (Mat (m+1)))
    (A : Fin 2 → Mat (m+1)) (hA : ∀ a, A a ∈ Q) (xs : List ℕ)
    (p : Fin m → Fin (m+1)) (a : Fin m → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, (A (a i)).mulVec (vector (entry xs (p i).val)) =
      vector (entry xs i.succ.val)) :
    ∀ i : Fin (m+1), ∃ L : Mat (m+1), L ∈ Q ∧
      L.mulVec (vector (entry xs 0)) = vector (entry xs i.val) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨A (a i) * L, Q.mul_mem (hA _) hL, ?_⟩
      rw [← mulVec_mulVec, he, hs i]

private theorem row_realizations {m : ℕ} (Q : Subalgebra (ZMod 2) (Mat (m+1)))
    (A : Fin 2 → Mat (m+1)) (hA : ∀ a, A a ∈ Q) (xs : List ℕ)
    (p : Fin m → Fin (m+1)) (a : Fin m → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, vecMul (vector (entry xs (p i).val)) (A (a i)) =
      vector (entry xs i.succ.val)) :
    ∀ i : Fin (m+1), ∃ R : Mat (m+1), R ∈ Q ∧
      vecMul (vector (entry xs 0)) R = vector (entry xs i.val) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * A (a i), Q.mul_mem hR (hA _), ?_⟩
      rw [← vecMul_vecMul, he, hs i]

theorem full_of_orbits {m : ℕ} (Q : Subalgebra (ZMod 2) (Mat (m+1)))
    (A : Fin 2 → Mat (m+1)) (hA : ∀ a, A a ∈ Q)
    (cols rows ci ri : List ℕ)
    (cp rp : Fin m → Fin (m+1)) (ca ra : Fin m → Fin 2)
    (hcp : ∀ i, cp i < i.succ) (hrp : ∀ i, rp i < i.succ)
    (hcs : ∀ i, (A (ca i)).mulVec (vector (entry cols (cp i).val)) =
      vector (entry cols i.succ.val))
    (hrs : ∀ i, vecMul (vector (entry rows (rp i).val)) (A (ra i)) =
      vector (entry rows i.succ.val))
    (hcl : cols.length = m+1) (hrl : rows.length = m+1)
    (hci : ∀ i : Fin (m+1), combineList cols (entry ci i.val) = 2 ^ i.val)
    (hri : ∀ i : Fin (m+1), combineList rows (entry ri i.val) = 2 ^ i.val)
    (huv : vecMulVec (vector (entry cols 0)) (vector (entry rows 0)) ∈ Q) : Q = ⊤ := by
  classical
  choose L hL heL using column_realizations Q A hA cols cp ca hcp hcs
  choose R hR heR using row_realizations Q A hA rows rp ra hrp hrs
  apply G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one Q
    (vector (entry cols 0)) (vector (entry rows 0)) L R hL hR huv
  · have he : (fun i => (L i).mulVec (vector (entry cols 0))) = matrix cols := funext heL
    rw [he]
    exact span_rows_of_inverse cols ci hcl hci
  · have he : (fun i => vecMul (vector (entry rows 0)) (R i)) = matrix rows := funext heR
    rw [he]
    exact span_rows_of_inverse rows ri hrl hri
end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate
