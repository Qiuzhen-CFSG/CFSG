module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Product

/-!
# Exhaustion of the unitary-five vector stabilizer

A determinant-one isometry of the Witt form fixing the first basis vector has
last row `(0,0,0,0,1)`. Its middle block is unitary, and its last column gives
the radical coordinates, including their trace relation. The remaining Gram
identities determine the first row. This proves the full matrix factorization
into a radical element and a special-unitary middle block. Conjugation by the
supplied Witt basis transports it to the actual identity-form SU₅.

Source: the classical parabolic calculation supporting Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks.Exhaustion
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

def middleBlock (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 5) (Fin 5) F :=
  !![1,0,0,0,0; 0,A 0 0,A 0 1,A 0 2,0;
     0,A 1 0,A 1 1,A 1 2,0; 0,A 2 0,A 2 1,A 2 2,0; 0,0,0,0,1]

theorem middleBlock_conjugate (c : F) (A : Matrix (Fin 3) (Fin 3) F) :
    wittBasisMatrix c * middleBlock A * wittBasisInverse c = leviMatrix A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittBasisMatrix, middleBlock, wittBasisInverse, leviMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

theorem middleBlock_det (A : Matrix (Fin 3) (Fin 3) F) : (middleBlock A).det = A.det := by
  have h := congrArg Matrix.det (middleBlock_conjugate (0 : F) A)
  have hi := congrArg Matrix.det (wittBasis_mul_inverse (0 : F))
  rw [det_mul, det_one] at hi
  rw [det_mul, det_mul, leviMatrix_det, mul_right_comm, hi, one_mul] at h
  exact h

theorem fixed_vector_decomposition (N : Matrix (Fin 5) (Fin 5) F)
    (hN : J.conjTranspose N * wittGram * N = wittGram)
    (hcol : ∀ i, N i 0 = if i = 0 then 1 else 0) (hdet : N.det = 1) :
    ∃ (u : Coord J) (A : (middleForm J).specialSubgroup),
      N = unipotentMatrix J u * middleBlock A.val.val := by
  have h (i j : Fin 5) := congrArg (fun X : Matrix (Fin 5) (Fin 5) F => X i j) hN
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ, wittGram] at h
  have hr (j : Fin 5) : N 4 j = if j = 4 then 1 else 0 := by
    have hh := h 0 j
    simp [hcol] at hh
    fin_cases j <;> simpa using hh
  let A : Matrix (Fin 3) (Fin 3) F := fun i j => N ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩
  have hA : (A.map J.conj).transpose * A = 1 := by
    ext i j
    have hh := h ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    fin_cases i <;> fin_cases j <;>
      simpa [A, Fin.sum_univ_succ, hr] using hh
  let AG : GL (Fin 3) F := ⟨A, (A.map J.conj).transpose, (mul_eq_one_comm.mp hA), hA⟩
  have ht : N 0 4 + J.conj (N 0 4) = pairing J ![N 1 4,N 2 4,N 3 4] ![N 1 4,N 2 4,N 3 4] := by
    have hh := h 4 4
    simp [hr] at hh
    simp only [pairing, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    apply CharTwo.add_eq_zero.mp
    convert hh using 1
    ring
  let u : Coord J := ⟨![N 1 4,N 2 4,N 3 4], N 0 4, ht⟩
  have hrow (j : Fin 3) : N 0 ⟨j.val + 1, by omega⟩ =
      J.conj (N 1 4) * A 0 j + J.conj (N 2 4) * A 1 j + J.conj (N 3 4) * A 2 j := by
    have hh := h 4 ⟨j.val + 1, by omega⟩
    fin_cases j <;> simp [hr] at hh <;>
      simpa [A, add_assoc] using CharTwo.add_eq_zero.mp hh
  have heq : N = unipotentMatrix J u * middleBlock A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentMatrix, middleBlock, Matrix.mul_apply, Fin.sum_univ_succ, u, A, hcol, hr]
    all_goals first | simpa [A, add_assoc] using hrow 0 | simpa [A, add_assoc] using hrow 1 | simpa [A, add_assoc] using hrow 2
  have hdA : A.det = 1 := by
    rw [heq, det_mul, unipotentMatrix_det, one_mul, middleBlock_det] at hdet
    exact hdet
  let AS : (middleForm J).specialSubgroup := ⟨AG, by
    rw [(middleForm J).mem_specialSubgroup_iff]
    constructor
    · change (A.map J.conj).transpose * 1 * A = 1
      simpa only [mul_one] using hA
    · exact Units.ext hdA⟩
  exact ⟨u, AS, heq⟩
omit [CharP F 2] in
private theorem adjoint_mul (A B : Matrix (Fin 5) (Fin 5) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((A * B).map J.conj).transpose = _
  rw [Matrix.map_mul, Matrix.transpose_mul]
  rfl

set_option maxRecDepth 2048 in
/-- Fixing the marked vector removes both diagonal torus parameters. -/
theorem fixed_lineVector_decomposition (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (g : J.specialSubgroup) (hg : linearAction J g lineVector = lineVector) :
    ∃ (u : Coord J) (A : (middleForm J).specialSubgroup),
      g = toSU J hJ u * leviSU J hJ A := by
  let B := wittBasisGL c
  let N : GL (Fin 5) F := B⁻¹ * g.val * B
  have hBN : B * N = g.val * B := by dsimp [N]; group
  have hBNv : B.val * N.val = g.val.val * B.val := congrArg Units.val hBN
  have hgram : J.conjTranspose B.val * J.form * B.val = wittGram :=
    wittBasis_gram J c hc hJ
  have hpres : J.conjTranspose N.val * wittGram * N.val = wittGram := by
    rw [← hgram]
    calc
      _ = J.conjTranspose (B.val * N.val) * J.form * (B.val * N.val) := by
        rw [adjoint_mul]; simp only [mul_assoc]
      _ = J.conjTranspose B.val * (J.conjTranspose g.val.val * J.form * g.val.val) * B.val := by
        rw [hBNv, adjoint_mul]; simp only [mul_assoc]
      _ = _ := by rw [g.property.1]
  let e : Fin 5 → F := ![1,0,0,0,0]
  have hBe : B.val *ᵥ e = lineVector := by
    ext i
    fin_cases i <;> simp [B, wittBasisGL, wittBasisMatrix, e, lineVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hNe : N.val *ᵥ e = e := by
    apply Matrix.mulVec_injective_of_isUnit B.isUnit
    rw [mulVec_mulVec, hBNv, ← mulVec_mulVec, hBe]
    exact hg
  have hcol (i : Fin 5) : N.val i 0 = if i = 0 then 1 else 0 := by
    have he := congrFun hNe i
    fin_cases i <;> simpa [e, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using he
  have hd : GeneralLinearGroup.det N = 1 := by
    dsimp [N]
    rw [map_mul, map_mul, map_inv, g.property.2, mul_one, inv_mul_cancel]
  obtain ⟨u, A, huA⟩ := fixed_vector_decomposition J N.val hpres hcol (congrArg Units.val hd)
  refine ⟨u, A, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have hback : g.val.val = B.val * N.val * (B⁻¹).val := by
    exact congrArg Units.val (show g.val = B * N * B⁻¹ by rw [hBN]; group)
  change g.val.val = (ambientGL J u).val * leviMatrix A.val.val
  rw [hback, huA, ambientGL_eq J c]
  change wittBasisMatrix c * (unipotentMatrix J u * middleBlock A.val.val) * wittBasisInverse c =
    (wittBasisMatrix c * unipotentMatrix J u * wittBasisInverse c) * leviMatrix A.val.val
  rw [← middleBlock_conjugate c A.val.val]
  simp only [mul_assoc, ← mul_assoc (wittBasisInverse c), wittBasis_inverse_mul, one_mul]

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks.Exhaustion
