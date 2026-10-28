module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Matrices
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# The plane Levi in the unitary-five model

A trace-one scalar changes the supplied flag basis to a hyperbolic basis whose
first two columns span the marked plane.  In that basis the Levi attached to
`A : GL₂(F)` is the block matrix
`diag (A, conj(det A) / det A, (A⁻¹)*)`.  Conjugating back gives an actual
special-unitary section of the restriction to the marked plane.
Restriction, exhaustion of its kernel and the projective quotient are proved
separately. This module constructs the matrix homomorphism and proves it
is special unitary.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(7), printed pp. 263--264, standard unitary parabolic calculation.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore

variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F)

/-- A hyperbolic correction of the supplied flag basis. -/
def planeBasis (c : F) : Matrix (Fin 5) (Fin 5) F :=
  !![1,0,0,c,0;
     1,0,0,c + 1,0;
     0,1,0,0,c;
     0,1,0,0,c + 1;
     0,0,1,0,0]

/-- The inverse of `planeBasis`. -/
def planeBasisInv (c : F) : Matrix (Fin 5) (Fin 5) F :=
  !![c + 1,c,0,0,0;
     0,0,c + 1,c,0;
     0,0,0,0,1;
     1,1,0,0,0;
     0,0,1,1,0]

theorem planeBasis_mul_inv (c : F) :
    planeBasis c * planeBasisInv c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBasis, planeBasisInv, Matrix.mul_apply, Fin.sum_univ_succ,
      CharTwo.add_self_eq_zero] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

theorem planeBasis_inv_mul (c : F) :
    planeBasisInv c * planeBasis c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBasis, planeBasisInv, Matrix.mul_apply, Fin.sum_univ_succ,
      CharTwo.add_self_eq_zero] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

def planeBasisGL (c : F) : GL (Fin 5) F :=
  ⟨planeBasis c, planeBasisInv c, planeBasis_mul_inv c, planeBasis_inv_mul c⟩

theorem planeBasis_gram (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    J.conjTranspose (planeBasis c) * J.form * planeBasis c =
      !![0,0,0,1,0;
         0,0,0,0,1;
         0,0,1,0,0;
         1,0,0,0,0;
         0,1,0,0,0] := by
  have hc' : J.conj c = c + 1 := by
    calc
      J.conj c = c + (c + J.conj c) := by simp [← add_assoc, CharTwo.add_self_eq_zero]
      _ = c + 1 := by rw [hc]
  rw [hJ, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBasis, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, hc', CharTwo.add_self_eq_zero, add_mul, mul_add,
      add_left_comm, add_assoc] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

/-- Conjugate transpose in the two-dimensional plane coordinates. -/
def planeAdjoint (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  (X.map J.conj).transpose

/-- The scalar used on the anisotropic middle line. -/
def planeMiddleScalar (A : GL (Fin 2) F) : F :=
  J.conj (A.val.det) * (A.val.det)⁻¹

/-- The corrected-basis block Levi matrix. -/
def planeBlockMatrix (A : GL (Fin 2) F) : Matrix (Fin 5) (Fin 5) F :=
  let d := planeMiddleScalar J A
  let D := planeAdjoint J (A.inv : Matrix (Fin 2) (Fin 2) F)
  !![A.val 0 0,A.val 0 1,0,0,0;
     A.val 1 0,A.val 1 1,0,0,0;
     0,0,d,0,0;
     0,0,0,D 0 0,D 0 1;
     0,0,0,D 1 0,D 1 1]

/-- The inverse block matrix, used to package the block as a `GL` element. -/
def planeBlockInvMatrix (A : GL (Fin 2) F) : Matrix (Fin 5) (Fin 5) F :=
  let d := planeMiddleScalar J A
  let D := planeAdjoint J (A.val : Matrix (Fin 2) (Fin 2) F)
  !![A.inv 0 0,A.inv 0 1,0,0,0;
     A.inv 1 0,A.inv 1 1,0,0,0;
     0,0,d⁻¹,0,0;
     0,0,0,D 0 0,D 0 1;
     0,0,0,D 1 0,D 1 1]

omit [CharP F 2] in
theorem planeMiddleScalar_ne_zero (A : GL (Fin 2) F) :
    planeMiddleScalar J A ≠ 0 := by
  have hdet : A.val.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse A.val_inv
  simp [planeMiddleScalar, hdet]

omit [CharP F 2] in
theorem planeBlock_mul_inv (A : GL (Fin 2) F) :
    planeBlockMatrix J A * planeBlockInvMatrix J A = 1 := by
  let d := planeMiddleScalar J A
  have hd : d ≠ 0 := planeMiddleScalar_ne_zero J A
  have hdet : A.val.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse A.val_inv
  have hA' : (A.val : Matrix (Fin 2) (Fin 2) F) * (A.val)⁻¹ = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact A.val_inv
  have hAi' : (A.val : Matrix (Fin 2) (Fin 2) F)⁻¹ * A.val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact A.inv_val
  have hA : (A.val : Matrix (Fin 2) (Fin 2) F) * A.inv = 1 := A.val_inv
  have hAi : A.inv * (A.val : Matrix (Fin 2) (Fin 2) F) = 1 := A.inv_val
  have hD : planeAdjoint J (A.inv : Matrix (Fin 2) (Fin 2) F) *
      planeAdjoint J (A.val : Matrix (Fin 2) (Fin 2) F) = 1 := by
    unfold planeAdjoint
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    simp
  have hD' := hD
  have hAij (i j : Fin 2) :
      ∑ k, A.val i k * (A.val)⁻¹ k j = (1 : Matrix (Fin 2) (Fin 2) F) i j :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X i j) hA'
  have hDij (i j : Fin 2) :
      ∑ k, J.conj (A.inv k i) * J.conj (A.val j k) =
        (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X i j) hD'
    simpa [planeAdjoint, Matrix.mul_apply, Fin.sum_univ_succ] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlockMatrix, planeBlockInvMatrix, planeAdjoint, Matrix.mul_apply,
      Fin.sum_univ_succ, d, hd] <;>
    first
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 0 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 0 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 1 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 1 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 0 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 0 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 1 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 1 1

omit [CharP F 2] in
theorem planeBlock_inv_mul (A : GL (Fin 2) F) :
    planeBlockInvMatrix J A * planeBlockMatrix J A = 1 := by
  let d := planeMiddleScalar J A
  have hd : d ≠ 0 := planeMiddleScalar_ne_zero J A
  have hA' : (A.val : Matrix (Fin 2) (Fin 2) F) * (A.val)⁻¹ = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact A.val_inv
  have hAi' : (A.val : Matrix (Fin 2) (Fin 2) F)⁻¹ * A.val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact A.inv_val
  have hA : (A.inv : Matrix (Fin 2) (Fin 2) F) * A.val = 1 := A.inv_val
  have hAi : (A.val : Matrix (Fin 2) (Fin 2) F) * A.inv = 1 := A.val_inv
  have hD : planeAdjoint J (A.val : Matrix (Fin 2) (Fin 2) F) *
      planeAdjoint J (A.inv : Matrix (Fin 2) (Fin 2) F) = 1 := by
    unfold planeAdjoint
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    simp
  have hD' := hD
  have hAij (i j : Fin 2) :
      ∑ k, (A.val)⁻¹ i k * A.val k j = (1 : Matrix (Fin 2) (Fin 2) F) i j :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X i j) hAi'
  have hDij (i j : Fin 2) :
      ∑ k, J.conj (A.val k i) * J.conj (A.inv j k) =
        (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X i j) hD'
    simpa [planeAdjoint, Matrix.mul_apply, Fin.sum_univ_succ] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlockMatrix, planeBlockInvMatrix, planeAdjoint, Matrix.mul_apply,
      Fin.sum_univ_succ, d, hd] <;>
    first
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 0 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 0 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 1 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hAij 1 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 0 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 0 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 1 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hDij 1 1

/-- The corrected-basis Levi embedding in `GL₅`. -/
def planeBlockGL : GL (Fin 2) F →* GL (Fin 5) F where
  toFun A := ⟨planeBlockMatrix J A, planeBlockInvMatrix J A,
    planeBlock_mul_inv J A, planeBlock_inv_mul J A⟩
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeBlockMatrix, planeMiddleScalar, planeAdjoint]
  map_mul' A B := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeBlockMatrix, planeMiddleScalar, planeAdjoint,
        Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_mul] <;> ring

/-- The actual Levi embedding into `GL₅` in the original coordinates. -/
def planeLeviGL (c : F) : GL (Fin 2) F →* GL (Fin 5) F :=
  (MulAut.conj (planeBasisGL (F := F) c)).toMonoidHom.comp
    (planeBlockGL J)

@[simp] theorem planeLeviGL_val (c : F) (A : GL (Fin 2) F) :
    (planeLeviGL J c A : Matrix (Fin 5) (Fin 5) F) =
      planeBasis c * planeBlockMatrix J A * planeBasisInv c := by
  change (planeBasisGL (F := F) c).val * (planeBlockGL J A).val *
    (planeBasisGL (F := F) c).inv = _
  change planeBasis c * planeBlockMatrix J A * planeBasisInv c = _
  rfl

def planeGram : Matrix (Fin 5) (Fin 5) F :=
  !![0,0,0,1,0;
     0,0,0,0,1;
     0,0,1,0,0;
     1,0,0,0,0;
     0,1,0,0,0]

omit [CharP F 2] in
theorem planeMiddleScalar_unitary (A : GL (Fin 2) F) :
    J.conj (planeMiddleScalar J A) * planeMiddleScalar J A = 1 := by
  let s : F := A.val.det
  have hs : s ≠ 0 := Matrix.det_ne_zero_of_right_inverse A.val_inv
  have hss : J.conj (J.conj s) = s := J.conj_involutive s
  have hcs : J.conj s ≠ 0 := by
    intro h
    apply hs
    rw [← hss, h]
    simp
  change J.conj (J.conj s * s⁻¹) * (J.conj s * s⁻¹) = 1
  rw [map_mul, hss]
  rw [map_inv₀]
  field_simp [hs, hcs]

omit [CharP F 2] in
theorem planeBlock_preserves (A : GL (Fin 2) F) :
    J.conjTranspose (planeBlockMatrix J A) * planeGram *
        planeBlockMatrix J A = planeGram := by
  let hA : (A.val : Matrix (Fin 2) (Fin 2) F) * (A.val)⁻¹ = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact A.val_inv
  let hAi : (A.val : Matrix (Fin 2) (Fin 2) F)⁻¹ * A.val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact A.inv_val
  have htop : planeAdjoint J (A.val : Matrix (Fin 2) (Fin 2) F) *
      planeAdjoint J (A.inv : Matrix (Fin 2) (Fin 2) F) = 1 := by
    unfold planeAdjoint
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    simp [hAi]
  have hbot : planeAdjoint J (A.inv : Matrix (Fin 2) (Fin 2) F) *
      planeAdjoint J (A.val : Matrix (Fin 2) (Fin 2) F) = 1 := by
    unfold planeAdjoint
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    simp [hA]
  have hmid := planeMiddleScalar_unitary J A
  have htopij (i j : Fin 2) :
      ∑ k, J.conj (A.val k i) * J.conj (A.inv j k) =
        (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X i j) htop
    simpa [planeAdjoint, Matrix.mul_apply, Fin.sum_univ_succ] using hh
  have hbotij (i j : Fin 2) :
      ∑ k, A.inv i k * A.val k j =
        (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X i j) hAi
    simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlockMatrix, planeGram, HermitianForm.conjTranspose,
      planeAdjoint, Matrix.mul_apply, Fin.sum_univ_succ, hmid] <;>
    first
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using htopij 0 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using htopij 0 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using htopij 1 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using htopij 1 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hbotij 0 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hbotij 0 1
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hbotij 1 0
    | simpa [Matrix.mul_apply, Fin.sum_univ_succ] using hbotij 1 1

omit [CharP F 2] in
theorem planeBlock_det (A : GL (Fin 2) F) :
    (planeBlockMatrix J A).det =
      A.val.det * planeMiddleScalar J A *
        (planeAdjoint J (A.inv : Matrix (Fin 2) (Fin 2) F)).det := by
  simp_rw [Matrix.det_succ_column_zero]
  simp [planeBlockMatrix, planeAdjoint, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  ring

omit [CharP F 2] in
theorem planeAdjoint_det (A : Matrix (Fin 2) (Fin 2) F) :
    (planeAdjoint J A).det = J.conj A.det := by
  unfold planeAdjoint
  rw [Matrix.det_transpose]
  exact (RingEquiv.map_det J.conj A).symm

omit [CharP F 2] in
theorem planeBlock_det_eq_one (A : GL (Fin 2) F) :
    (planeBlockMatrix J A).det = 1 := by
  have hdet : A.val.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse A.val_inv
  have hprod : A.val.det * A.inv.det = 1 := by
    have h := congrArg Matrix.det A.val_inv
    simpa only [Matrix.det_mul, Matrix.det_one] using h
  have hdetinv : A.inv.det = (A.val.det)⁻¹ := by
    field_simp [hdet] at hprod ⊢
    exact hprod
  rw [planeBlock_det, planeAdjoint_det, hdetinv]
  rw [map_inv₀]
  simp only [planeMiddleScalar]
  field_simp [hdet]

theorem planeLeviGL_det (c : F) (A : GL (Fin 2) F) :
    (planeLeviGL J c A).val.det = 1 := by
  rw [planeLeviGL_val]
  rw [Matrix.det_mul, Matrix.det_mul, planeBlock_det_eq_one]
  have hP : planeBasis c * planeBasisInv c = 1 := planeBasis_mul_inv c
  have hdetP : (planeBasis c).det * (planeBasisInv c).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hP
  calc
    (planeBasis c).det * 1 * (planeBasisInv c).det =
        (planeBasis c).det * (planeBasisInv c).det := by ring
    _ = 1 := hdetP

set_option maxRecDepth 2048 in
theorem planeLeviGL_mem_special (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : GL (Fin 2) F) :
    planeLeviGL J c A ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [planeLeviGL_val]
    let P := planeBasis c
    let Pi := planeBasisInv c
    let B := planeBlockMatrix J A
    have hgram : J.conjTranspose P * J.form * P = planeGram := by
      simpa [P, planeGram] using planeBasis_gram J c hc hJ
    have hblock : J.conjTranspose B * planeGram * B = planeGram :=
      planeBlock_preserves J A
    have hPiP : Pi * P = 1 := planeBasis_inv_mul c
    have hPPi : P * Pi = 1 := planeBasis_mul_inv c
    have hPiStarPStar : J.conjTranspose Pi * J.conjTranspose P = 1 := by
      change (Pi.map J.conj).transpose * (P.map J.conj).transpose = 1
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPPi]
      simp
    have hctmul (X Y : Matrix (Fin 5) (Fin 5) F) :
        J.conjTranspose (X * Y) = J.conjTranspose Y * J.conjTranspose X := by
      change ((X * Y).map J.conj).transpose =
        (Y.map J.conj).transpose * (X.map J.conj).transpose
      rw [Matrix.map_mul, Matrix.transpose_mul]
    calc
      J.conjTranspose (P * B * Pi) * J.form * (P * B * Pi) =
          J.conjTranspose Pi * J.conjTranspose B *
            (J.conjTranspose P * J.form * P) * B * Pi := by
              rw [hctmul, hctmul]
              simp only [mul_assoc]
      _ = J.conjTranspose Pi * J.conjTranspose B * planeGram * B * Pi := by
            rw [hgram]
      _ = J.conjTranspose Pi * (J.conjTranspose B * planeGram * B) * Pi := by
            simp only [mul_assoc]
      _ = J.conjTranspose Pi * planeGram * Pi := by rw [hblock]
      _ = J.form := by
        calc
          J.conjTranspose Pi * planeGram * Pi =
              J.conjTranspose Pi * (J.conjTranspose P * J.form * P) * Pi := by rw [hgram]
          _ =
              (J.conjTranspose Pi * J.conjTranspose P) * J.form * (P * Pi) := by
                simp only [mul_assoc]
          _ = J.form := by rw [hPiStarPStar, hPPi]; simp
  · apply Units.ext
    exact planeLeviGL_det J c A

def planeLeviSU (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    GL (Fin 2) F →* J.specialSubgroup :=
  (planeLeviGL J c).codRestrict _ (planeLeviGL_mem_special J c hc hJ)

@[simp] theorem planeLeviSU_val (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (A : GL (Fin 2) F) :
    (planeLeviSU J c hc hJ A).val =
      planeLeviGL J c A := rfl

/-- The special-linear part of the plane Levi. -/
def planeSLtoGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F where
  toFun A := Matrix.GeneralLinearGroup.mkOfDetNeZero A.1 (by rw [A.2]; simp)
  map_one' := by
    apply Units.ext
    rfl
  map_mul' A B := by
    apply Units.ext
    rfl

def planeLeviSL (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F →* J.specialSubgroup :=
  (planeLeviSU J c hc hJ).comp (planeSLtoGL (F := F))

omit [CharP F 2] in
@[simp] theorem planeSLtoGL_det (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (planeSLtoGL A).val.det = 1 := by
  change A.1.det = 1
  exact A.2


end Theory.SpecificGroups.UnitaryFive.PlaneCore
