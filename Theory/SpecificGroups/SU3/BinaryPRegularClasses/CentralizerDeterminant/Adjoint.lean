module
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.TraceParameters

/-!
# Adjoint correction in a unitary centralizer

The adjoint is formed with the original nondegenerate Gram matrix. It reverses
products, is involutive, and preserves the linear centralizer of a unitary
matrix. If a centralizing invertible matrix commutes with its adjoint, their
quotient is unitary. No definiteness, distinct-eigenvalue, or standard-form
assumption is used.

This supplies the geometric correction for the SU₃ class-count argument
associated with GLS III 2.8.2, 2.8.6(a), and 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`. Construction of normal centralizer witnesses
is a separate mathematical obligation.
-/

open Matrix BenderSuzuki.MatrixGroups
noncomputable section
namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
variable {F : Type*} [Field F] {n : ℕ}

private theorem ct_mul (J : HermitianForm n F) (A B : Matrix (Fin n) (Fin n) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem ct_one (J : HermitianForm n F) : J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

private def ctUnit (J : HermitianForm n F) (A : GL (Fin n) F) : GL (Fin n) F where
  val := J.conjTranspose A.val
  inv := J.conjTranspose (A⁻¹).val
  val_inv := by rw [← ct_mul]; simpa using ct_one J
  inv_val := by rw [← ct_mul]; simpa using ct_one J

private theorem ctUnit_mul (J : HermitianForm n F) (A B : GL (Fin n) F) :
    ctUnit J (A * B) = ctUnit J B * ctUnit J A := Units.ext (ct_mul J _ _)

private theorem ctUnit_inv (J : HermitianForm n F) (A : GL (Fin n) F) :
    ctUnit J A⁻¹ = (ctUnit J A)⁻¹ := Units.ext rfl

private theorem ctUnit_twice (J : HermitianForm n F) (A : GL (Fin n) F) :
    ctUnit J (ctUnit J A) = A := by
  apply Units.ext
  ext i j
  exact J.conj_involutive _

private def gramUnit (J : HermitianForm n F) : GL (Fin n) F :=
  GeneralLinearGroup.mkOfDetNeZero J.form J.form_nondegenerate

private theorem ctUnit_gram (J : HermitianForm n F) : ctUnit J (gramUnit J) = gramUnit J := by
  apply Units.ext
  ext i j
  exact J.form_hermitian i j

/-- The adjoint for the original Gram matrix, as an invertible matrix. -/
public def adjoint (J : HermitianForm n F) (A : GL (Fin n) F) : GL (Fin n) F :=
  (gramUnit J)⁻¹ * ctUnit J A * gramUnit J

public theorem adjoint_val (J : HermitianForm n F) (A : GL (Fin n) F) :
    (adjoint J A).val = J.form⁻¹ * J.conjTranspose A.val * J.form := by
  change (↑((gramUnit J)⁻¹) : Matrix (Fin n) (Fin n) F) * _ * _ = _
  rw [GeneralLinearGroup.coe_inv]
  rfl

public theorem adjoint_mul (J : HermitianForm n F) (A B : GL (Fin n) F) :
    adjoint J (A * B) = adjoint J B * adjoint J A := by
  simp only [adjoint, ctUnit_mul, mul_assoc, mul_inv_cancel_left]

@[simp] public theorem adjoint_inv (J : HermitianForm n F) (A : GL (Fin n) F) :
    adjoint J A⁻¹ = (adjoint J A)⁻¹ := by
  simp only [adjoint, ctUnit_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]

@[simp] public theorem adjoint_twice (J : HermitianForm n F) (A : GL (Fin n) F) :
    adjoint J (adjoint J A) = A := by
  simp only [adjoint, ctUnit_mul, ctUnit_inv, ctUnit_twice, ctUnit_gram,
    mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

public theorem mem_unitary_iff_adjoint (J : HermitianForm n F) (A : GL (Fin n) F) :
    A ∈ J.unitarySubgroup ↔ adjoint J A = A⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← mul_left_cancel_iff (a := gramUnit J)]
  simp only [adjoint, ← mul_assoc, mul_inv_cancel, one_mul, mul_one]
  rw [Units.ext_iff]
  exact J.mem_unitarySubgroup_iff A

public theorem det_adjoint (J : HermitianForm n F) (A : GL (Fin n) F) :
    (GeneralLinearGroup.det (adjoint J A) : F) = J.conj (GeneralLinearGroup.det A : F) := by
  have hdet : GeneralLinearGroup.det (adjoint J A) = GeneralLinearGroup.det (ctUnit J A) := by
    simp only [adjoint, map_mul, map_inv, mul_comm, mul_left_comm, mul_inv_cancel, one_mul]
  rw [hdet, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
  change ((A.val.map J.conj).transpose).det = _
  rw [det_transpose]
  exact (J.conj.map_det A.val).symm

/-- Taking adjoints preserves the centralizer of a unitary element. -/
public theorem commute_adjoint (J : HermitianForm n F) (g : J.unitarySubgroup)
    (A : GL (Fin n) F) (hA : Commute A g.val) : Commute (adjoint J A) g.val := by
  have he := congrArg (adjoint J) hA.eq
  rw [adjoint_mul, adjoint_mul, (mem_unitary_iff_adjoint J g.val).mp g.property] at he
  have hc : Commute g.val⁻¹ (adjoint J A) := he
  simpa using hc.symm.inv_right

/-- For a normal invertible matrix, division by its adjoint is unitary. -/
public theorem polarRatio_mem_unitary (J : HermitianForm n F) (A : GL (Fin n) F)
    (hA : Commute A (adjoint J A)) : A * (adjoint J A)⁻¹ ∈ J.unitarySubgroup := by
  rw [mem_unitary_iff_adjoint, adjoint_mul, adjoint_inv, adjoint_twice, _root_.mul_inv_rev, inv_inv]
  exact hA.symm.inv_right.eq.symm

end Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
