module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.SU3.MarkedHyperbolicCoordinates
public import Theory.SpecificGroups.SU3.CyclicCoreSylow.Generators

/-!
# The determinant-corrected hyperbolic plane in SU₃

The plane occupies coordinates 0 and 2 of the antidiagonal ternary form.
Its determinant inverse occupies coordinate 1. The resulting homomorphism
is compatible with entrywise field conjugation, including after projective
descent and passage to inner automorphisms.

Source: Aschbacher–Smith A.3.21(a), p.55, and E.1.14(7), p.214.
-/

public section
open Matrix Subgroup BenderSuzuki.External Matrix.UnitaryQuaternionRotation
namespace BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- The hyperbolic plane with the original field involution. -/
@[expose] def plane : HermitianForm 2 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := !![0,1;1,0]
  form_hermitian := by intro i j; fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by simp [Matrix.det_fin_two]

/-- Insert the inverse determinant on the orthogonal middle line. -/
@[expose] def blockMatrix (A : GL (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0,0,A 0 1;0,↑((GeneralLinearGroup.det A)⁻¹),0;A 1 0,0,A 1 1]

theorem blockMatrix_det (A : GL (Fin 2) F) : (blockMatrix A).det = 1 := by
  have hd : (A 0 0 * A 1 1 - A 0 1 * A 1 0) *
      (↑((GeneralLinearGroup.det A)⁻¹) : F) = 1 := by
    simpa [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using
      (Units.val_mul (GeneralLinearGroup.det A) (GeneralLinearGroup.det A)⁻¹).symm
  simp only [Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply] at hd
  simp [blockMatrix, Matrix.det_fin_three]
  linear_combination hd

@[expose] def blockSL : GL (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun A := ⟨blockMatrix A, blockMatrix_det A⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change blockMatrix (A * B) = blockMatrix A * blockMatrix B
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, mul_comm]

private theorem det_norm (A : (plane J).unitarySubgroup) :
    J.conj A.val.val.det * A.val.val.det = 1 := by
  have h := A.property
  rw [(plane J).mem_unitarySubgroup_iff] at h
  have hd := congrArg Matrix.det h
  change (((A.val.val.map J.conj).transpose * (plane J).form) * A.val.val).det =
    (plane J).form.det at hd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  change (J.conj.mapMatrix A.val.val).det * (plane J).form.det * A.val.val.det =
    (plane J).form.det at hd
  rw [← J.conj.map_det] at hd
  rw [show (plane J).form.det = -1 by simp [plane, Matrix.det_fin_two]] at hd
  linear_combination -hd

theorem block_unitary (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (A : (plane J).unitarySubgroup) :
    SpecialLinearGroup.toGL (blockSL A.val) ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (blockMatrix A.val) * J.form * blockMatrix A.val = J.form
  have h := ((plane J).mem_unitarySubgroup_iff A.val).mp A.property
  have he (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) h
  have hd := det_norm J A
  have hi : J.conj A.val.val.det⁻¹ * A.val.val.det⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hd, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, HermitianForm.conjTranspose, hJ, Matrix.mul_apply, Fin.sum_univ_three]
  · simpa [plane, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 0 0
  · simpa [plane, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 0 1
  · simpa only [map_inv₀] using hi
  · simpa [plane, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 1 0
  · simpa [plane, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two] using he 1 1

/-- The full unitary plane maps into the special ternary group. -/
@[expose] def block (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    (plane J).unitarySubgroup →* J.specialSubgroup :=
  ((SpecialLinearGroup.toGL.comp blockSL).comp (plane J).unitarySubgroup.subtype).codRestrict
    J.specialSubgroup (by intro A; exact ⟨block_unitary J hJ A, by simp⟩)

/-- Its literal projective image, without an injectivity assumption. -/
@[expose] def projectiveBlock (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    (plane J).unitarySubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective.comp (block J hJ)

/-- The plane acts through the actual inner-automorphism subgroup. -/
@[expose] def innerBlock (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    (plane J).unitarySubgroup →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  MulAut.conj.comp (projectiveBlock J hJ)

theorem innerBlock_mem (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (A : (plane J).unitarySubgroup) :
    innerBlock J hJ A ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  ⟨projectiveBlock J hJ A, rfl⟩


variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- Scalar minus one on the plane is the ternary diagonal involution. -/
theorem projectiveBlock_minusOne :
    projectiveBlock J hJ (minusOne (plane J) rfl) = hermitianTorusPSU J hJ (-1) := by
  apply Subtype.ext
  simp only [projectiveBlock, MonoidHom.comp_apply, specialToProjective_apply_val,
    hermitianTorusPSU_val]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  change blockMatrix (GeneralLinearGroup.scalar (Fin 2) (-1)) = hermitianTorusMatrix J (-1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      hermitianTorusMatrix]

/-- The repository torus uses its last coordinate as parameter. Thus the
plane rotation with first entry r has repository parameter -r⁻¹. -/
theorem projectiveBlock_torus (r : Fˣ) (hr : J.conj (r : F) = -(r : F)) :
    projectiveBlock J hJ (torus (plane J) rfl r hr) =
      hermitianTorusPSU J hJ (-r⁻¹) := by
  apply Subtype.ext
  simp only [projectiveBlock, MonoidHom.comp_apply, specialToProjective_apply_val,
    hermitianTorusPSU_val]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  change blockMatrix (torusGL r) = hermitianTorusMatrix J (-r⁻¹)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, torusGL, GeneralLinearGroup.diagonalPair, Matrix.det_fin_two,
      hermitianTorusMatrix, hr]

/-- The swap has determinant minus one, corrected on the middle line. -/
theorem projectiveBlock_swap :
    projectiveBlock J hJ (swap (plane J) rfl) = hermitianWeylPSU J hJ := by
  apply Subtype.ext
  simp only [projectiveBlock, MonoidHom.comp_apply, specialToProjective_apply_val,
    hermitianWeylPSU_val]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  change blockMatrix (GeneralLinearGroup.coordinateSwap F) = hermitianWeylMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, GeneralLinearGroup.coordinateSwap, Matrix.det_fin_two,
      hermitianWeylMatrix]

open OddPrimeSylow.NormalizedOuter

theorem projectiveBlock_fieldConj (A : (plane J).unitarySubgroup) :
    entrywiseProjectiveAut J hJ (projectiveBlock J hJ A) =
      projectiveBlock J hJ (fieldConj (plane J) rfl A) := by
  change entrywiseProjectiveAut J hJ (J.specialToProjective (block J hJ A)) =
    J.specialToProjective (block J hJ (fieldConj (plane J) rfl A))
  rw [entrywiseProjectiveAut_specialToProjective]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [entrywiseSpecialAut_apply_val]
  change (blockMatrix A.val).map J.conj =
    blockMatrix (GeneralLinearGroup.map J.conj.toRingHom A.val)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, Matrix.det_fin_two]

/-- Entrywise Frobenius acts on the entire plane image. -/
theorem innerBlock_fieldConj (A : (plane J).unitarySubgroup) :
    entrywiseProjectiveAut J hJ * innerBlock J hJ A * (entrywiseProjectiveAut J hJ)⁻¹ =
      innerBlock J hJ (fieldConj (plane J) rfl A) := by
  have h (c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
      (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      c * MulAut.conj x * c⁻¹ = MulAut.conj (c x) := by ext y; simp
  change _ * MulAut.conj (projectiveBlock J hJ A) * _ =
    MulAut.conj (projectiveBlock J hJ (fieldConj (plane J) rfl A))
  rw [h, projectiveBlock_fieldConj]

end BenderSuzuki.MatrixGroups.HermitianForm.MarkedHyperbolicModel
