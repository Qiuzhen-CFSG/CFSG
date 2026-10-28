module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalReduction

/-!
# Row reconstruction of the J₄ local commutant

A cyclic row basis determines a commuting matrix from its zeroth row. A sum
of actual centralizer elements annihilating that row imposes a two-dimensional
constraint, which determines the whole matrix. Numerical certificates are
supplied by the sibling modules; no generation assertion about the centralizer
is required. The concrete generators are the ATLAS matrices in `Model.Data`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
open Matrix

abbrev localMatrix (c : involutionCentralizer) : BinaryMatrix :=
  ((c : BinaryMatrixˣ) : BinaryMatrix)

theorem localMatrix_commutes_a (c : involutionCentralizer) :
    localMatrix c * matrixA = matrixA * localMatrix c := by
  have hc := ((mem_involutionCentralizer_iff _).mp c.property).2
  exact @congrArg BinaryMatrixˣ BinaryMatrix
    ((c : BinaryMatrixˣ) * matrixUnitA) (matrixUnitA * (c : BinaryMatrixˣ))
    Units.val hc

theorem commutes_sum (M : BinaryMatrix)
    (h : ∀ c : involutionCentralizer, M * localMatrix c = localMatrix c * M)
    (L : List involutionCentralizer) :
    M * (L.map localMatrix).sum = (L.map localMatrix).sum * M := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, add_mul, h c, ih]

/-- The sparse projection used to bound the left kernel of the annihilator. -/
def rowProjection : BinaryMatrix :=
  1 + vecMulVec (Pi.single 0 1) ((1 : BinaryMatrix) 0) +
    vecMulVec (Pi.single 1 1) (matrixA 0)

theorem rowProjection_kernel (x : Fin 112 → ZMod 2)
    (hx : x ᵥ* rowProjection = 0) :
    x = x 0 • ((1 : BinaryMatrix) 0) + x 1 • (matrixA 0) := by
  rw [rowProjection, vecMul_add, vecMul_add, vecMul_one,
    vecMul_vecMulVec, vecMul_vecMulVec, dotProduct_single_one,
    dotProduct_single_one, add_assoc] at hx
  funext j
  exact CharTwo.add_eq_zero.mp (congrFun hx j)

/-- Pure row reconstruction, kept polymorphic to avoid reducing binary arithmetic
while applying the matrix identities. -/
private theorem matrix_eq_span_of_cyclic_rows
    {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (o : n) (W : n → Matrix n n K) (A Q Qi R M : Matrix n n K)
    (hQ : ∀ i, Q i = W i o) (hQi : Qi * Q = 1)
    (hWA : ∀ i, W i * A = A * W i)
    (hWM : ∀ i, M * W i = W i * M)
    (hMR : M * R = R * M) (hR0 : R o = 0)
    (hker : ∀ x : n → K, x ᵥ* R = 0 →
      ∃ r s : K, x = r • ((1 : Matrix n n K) o) + s • (A o)) :
    ∃ r s : K, M = r • (1 : Matrix n n K) + s • A := by
  have hzero : M o ᵥ* R = 0 := by
    rw [← mul_apply_eq_vecMul, hMR, mul_apply_eq_vecMul, hR0, zero_vecMul]
  obtain ⟨r, s, hrs⟩ := hker (M o) hzero
  refine ⟨r, s, ?_⟩
  let N : Matrix n n K := r • 1 + s • A
  have hN0 : M o = N o := hrs
  have hN (i : n) : N * W i = W i * N := by
    dsimp only [N]
    rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_smul, one_mul, mul_one, hWA]
  have heq : Q * M = Q * N := by
    funext i
    rw [mul_apply_eq_vecMul, mul_apply_eq_vecMul, hQ,
      ← mul_apply_eq_vecMul, ← mul_apply_eq_vecMul, ← hWM i, ← hN i,
      mul_apply_eq_vecMul, mul_apply_eq_vecMul, hN0]
  calc
    M = (Qi * Q) * M := by rw [hQi, one_mul]
    _ = Qi * (Q * M) := mul_assoc _ _ _
    _ = Qi * (Q * N) := by rw [heq]
    _ = N := by rw [← mul_assoc, hQi, one_mul]

/-- A left inverse of the cyclic matrix and a two-dimensional left-kernel
certificate force the claimed commutant. All finite inputs are explicit. -/
theorem commutant_of_certificates
    (W : Fin 112 → involutionCentralizer) (Q Qi R : BinaryMatrix)
    (L : List involutionCentralizer)
    (hQ : ∀ i, Q i = localMatrix (W i) 0)
    (hQi : Qi * Q = 1)
    (hR : R = (L.map localMatrix).sum)
    (hR0 : R 0 = 0)
    (hker : ∀ x : Fin 112 → ZMod 2, x ᵥ* R = 0 →
      ∃ r s : ZMod 2, x = r • ((1 : BinaryMatrix) 0) + s • (matrixA 0)) :
    LocalMatrixCommutant := by
  intro M hM
  apply matrix_eq_span_of_cyclic_rows 0 (fun i => localMatrix (W i))
    matrixA Q Qi R M hQ hQi (fun i => localMatrix_commutes_a (W i))
    (fun i => hM (W i)) _ hR0 hker
  rw [hR]
  exact commutes_sum M hM L

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
