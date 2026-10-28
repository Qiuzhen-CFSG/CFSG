module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate.PackedRows
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion

/-!
# Packed arithmetic and orbit criteria over the cubic coefficient field

PackedRows supplies the proved interpretation of addition, scalar multiplication
and products. These small adapters certify rank-one matrices and their orbit
bases. A left inverse proves spanning; induction on the recorded parents
realizes each vector by an element of the generated algebra. The existing
rank-one criterion then gives the entire matrix algebra.

The actual consumer is Density84 for the fixed SU₃(5) middle quotient.
Source motivation: Guralnick–Malle Proposition 4.3, p.10, and
Aschbacher–Smith K.2, p.453.
-/

@[expose] public section
open Matrix
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
variable {k : Type*} [Field k] {n : ℕ}

theorem span_rows_of_left_inverse (C D : Matrix (Fin n) (Fin n) k)
    (h : D * C = 1) : Submodule.span k (Set.range C) = ⊤ := by
  change Submodule.span k (Set.range C.row) = ⊤
  rw [← range_vecMulLinear C]
  apply LinearMap.range_eq_top.mpr
  intro x
  refine ⟨Matrix.vecMul x D, ?_⟩
  change Matrix.vecMul (Matrix.vecMul x D) C = x
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

private theorem column_orbit (Q : Subalgebra k (Matrix (Fin (n+1)) (Fin (n+1)) k))
    (G : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) k) (hG : ∀ a, G a ∈ Q)
    (C : Fin (n+1) → Fin (n+1) → k)
    (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ j, (p j).val < j.val + 1)
    (hC : ∀ j, C j.succ = (G (a j)).mulVec (C (p j))) :
    ∀ i, ∃ M ∈ Q, M.mulVec (C 0) = C i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, Matrix.one_mulVec _⟩
    | succ i =>
      obtain ⟨M, hM, he⟩ := ih (p i) (hp i)
      refine ⟨G (a i) * M, Q.mul_mem (hG _) hM, ?_⟩
      rw [← Matrix.mulVec_mulVec, he, ← hC i]

private theorem row_orbit (Q : Subalgebra k (Matrix (Fin (n+1)) (Fin (n+1)) k))
    (G : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) k) (hG : ∀ a, G a ∈ Q)
    (C : Fin (n+1) → Fin (n+1) → k)
    (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ j, (p j).val < j.val + 1)
    (hC : ∀ j, C j.succ = Matrix.vecMul (C (p j)) (G (a j))) :
    ∀ i, ∃ M ∈ Q, Matrix.vecMul (C 0) M = C i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, Matrix.vecMul_one _⟩
    | succ i =>
      obtain ⟨M, hM, he⟩ := ih (p i) (hp i)
      refine ⟨M * G (a i), Q.mul_mem hM (hG _), ?_⟩
      rw [← Matrix.vecMul_vecMul, he, ← hC i]

theorem density_of_orbits
    (G : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) k)
    (C R : Matrix (Fin (n+1)) (Fin (n+1)) k)
    (cp rp : Fin n → Fin (n+1)) (ca ra : Fin n → Fin 2)
    (hcp : ∀ j, (cp j).val < j.val + 1) (hrp : ∀ j, (rp j).val < j.val + 1)
    (hC : ∀ j, C j.succ = (G (ca j)).mulVec (C (cp j)))
    (hR : ∀ j, R j.succ = Matrix.vecMul (R (rp j)) (G (ra j)))
    (hCs : Submodule.span k (Set.range C) = ⊤)
    (hRs : Submodule.span k (Set.range R) = ⊤)
    (Q : Subalgebra k (Matrix (Fin (n+1)) (Fin (n+1)) k))
    (hG : ∀ a, G a ∈ Q) (huv : Matrix.vecMulVec (C 0) (R 0) ∈ Q) : Q = ⊤ := by
  apply G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one
    Q (C 0) (R 0) (fun M : Q => M.val) (fun M : Q => M.val)
    (fun M => M.property) (fun M => M.property) huv
  · apply top_unique
    rw [← hCs]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    obtain ⟨M, hM, he⟩ := column_orbit Q G hG C cp ca hcp hC i
    exact ⟨⟨M, hM⟩, he⟩
  · apply top_unique
    rw [← hRs]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    obtain ⟨M, hM, he⟩ := row_orbit Q G hG R rp ra hrp hR i
    exact ⟨⟨M, hM⟩, he⟩
end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84

namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
open Certificate.Packed

def vector {n : ℕ} (r : Row) : Fin n → CoefficientField := fun j => entry r j.val

def rowProduct {n : ℕ} (r : Row) (A : Fin n → Row) : Row :=
  mul (fun _ : Fin 1 => r) A 0

theorem rowProduct_correct {n m : ℕ} (r : Row) (A : Fin n → Row) :
    vector (n := m) (rowProduct r A) = Matrix.vecMul (vector r) (matrix m A) := by
  exact congrArg (fun M : Matrix (Fin 1) (Fin m) CoefficientField => M 0)
    (matrix_mul (p := m) (fun _ : Fin 1 => r) A)

theorem rank_one_correct {n : ℕ} (u v : Row) :
    matrix n (fun i : Fin n => scale (u.1.testBit i.val) (u.2.testBit i.val) v) =
      Matrix.vecMulVec (vector u) (vector v) := by
  apply Matrix.ext
  intro i j
  exact entry_scale _ _ _ _

theorem transpose_correct {n : ℕ} (A T : Fin n → Row)
    (h : ∀ i j, ((T i).1.testBit j.val, (T i).2.testBit j.val) =
      ((A j).1.testBit i.val, (A j).2.testBit i.val)) :
    matrix n T = (matrix n A).transpose := by
  apply Matrix.ext
  intro i j
  have h1 := congrArg Prod.fst (h i j)
  have h2 := congrArg Prod.snd (h i j)
  dsimp only at h1 h2
  simp only [matrix, entry, Matrix.transpose_apply, h1, h2]

theorem matrix_add_rows {n : ℕ} (a b : Fin n → Row) :
    matrix n (fun i => add (a i) (b i)) = matrix n a + matrix n b := by
  apply Matrix.ext
  intro i j
  exact entry_add _ _ _

theorem matrix_scale_rows {n : ℕ} (a b : Bool) (r : Fin n → Row) :
    matrix n (fun i => scale a b (r i)) =
      (⟨if a then 1 else 0, if b then 1 else 0⟩ : CoefficientField) • matrix n r := by
  apply Matrix.ext
  intro i j
  exact entry_scale _ _ _ _

theorem mul_mem_checked {n : ℕ}
    (Q : Subalgebra CoefficientField (Matrix (Fin n) (Fin n) CoefficientField))
    (a b c : Fin n → Row) (ha : matrix n a ∈ Q) (hb : matrix n b ∈ Q)
    (h : ∀ i, mul a b i = c i) : matrix n c ∈ Q := by
  rw [← funext h, matrix_mul]
  exact Q.mul_mem ha hb

theorem add_mem_checked {n : ℕ}
    (Q : Subalgebra CoefficientField (Matrix (Fin n) (Fin n) CoefficientField))
    (a b c : Fin n → Row) (ha : matrix n a ∈ Q) (hb : matrix n b ∈ Q)
    (h : ∀ i, add (a i) (b i) = c i) : matrix n c ∈ Q := by
  rw [← funext h, matrix_add_rows]
  exact Q.add_mem ha hb

theorem scale_mem_checked {n : ℕ}
    (Q : Subalgebra CoefficientField (Matrix (Fin n) (Fin n) CoefficientField))
    (a b : Bool) (r s : Fin n → Row) (hr : matrix n r ∈ Q)
    (h : ∀ i, scale a b (r i) = s i) : matrix n s ∈ Q := by
  rw [← funext h, matrix_scale_rows]
  exact Q.smul_mem hr _
end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates.Density84
