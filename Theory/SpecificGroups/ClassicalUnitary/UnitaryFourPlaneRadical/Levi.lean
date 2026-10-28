module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
import Mathlib.Algebra.CharP.Two

/-!+# An SL₂ section of the unitary-four plane restriction

For the antidiagonal Hermitian form, a determinant-one matrix A lifts to the
literal block diagonal matrix diag(A, σ(A)). In characteristic two the identity
Aᵀ S A = S, with S reversing two coordinates, proves that this lift is unitary.
Its determinant is det(A) σ(det(A)) = 1. Thus it belongs to the determinant-one
plane local, and multiplication of the two diagonal blocks makes it a
homomorphism. Restriction recovers A, so the published restriction is surjective.

This supplies the surjectivity input for the plane-local calculation underlying
Aschbacher--Smith F.1.12(I)(6), printed pp.263–264 of `refs/quasithin.pdf`.
There is no field-size restriction, in particular none excluding the matrix
field GF(4) of the q = 2 case. The two-core and quotient assembly is separate.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
variable (F : Type*) [Field F] (σ : F ≃+* F)

/-- The literal block diagonal matrix `diag(A, A.map σ)` in the flag coordinates. -/
def leviMatrix (A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0,A 0 1,0,0; A 1 0,A 1 1,0,0;
     0,0,σ (A 0 0),σ (A 0 1); 0,0,σ (A 1 0),σ (A 1 1)]

theorem leviMatrix_one : leviMatrix F σ 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMatrix]

theorem leviMatrix_mul (A B : SpecialLinearGroup (Fin 2) F) :
    leviMatrix F σ (A * B) = leviMatrix F σ A * leviMatrix F σ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]

theorem leviMatrix_det (A : SpecialLinearGroup (Fin 2) F) :
    (leviMatrix F σ A).det = 1 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  calc
    (leviMatrix F σ A).det =
        (A 0 0 * A 1 1 - A 0 1 * A 1 0) *
          σ (A 0 0 * A 1 1 - A 0 1 * A 1 0) := by
      rw [Matrix.det_succ_row_zero]
      simp [leviMatrix, Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
      ring
    _ = 1 := by rw [hd, map_one, mul_one]

variable (hσ : Function.Involutive σ) [CharP F 2]

theorem leviMatrix_unitary (A : SpecialLinearGroup (Fin 2) F) :
    (form F σ hσ).conjTranspose (leviMatrix F σ A) * gram F *
      leviMatrix F σ A = gram F := by
  have hd : A 0 0 * A 1 1 + A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, CharTwo.sub_eq_add] using A.property
  have hdc : σ (A 0 0) * σ (A 1 1) + σ (A 0 1) * σ (A 1 0) = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg σ hd
  have hl : (form F σ hσ).conjTranspose (leviMatrix F σ A) * gram F =
      !![0,0,σ (A 1 0),σ (A 0 0); 0,0,σ (A 1 1),σ (A 0 1);
         A 1 0,A 0 0,0,0; A 1 1,A 0 1,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [form, gram, leviMatrix, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals exact hσ _
  rw [hl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, leviMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      mul_comm, CharTwo.add_self_eq_zero]
  all_goals first
    | simpa only [mul_comm, add_comm] using hd
    | simpa only [mul_comm, add_comm] using hdc

/-- The block diagonal lift as an actual special unitary element. -/
def leviSU (A : SpecialLinearGroup (Fin 2) F) : SU F (form F σ hσ) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (leviMatrix F σ A)
    (by rw [leviMatrix_det]; exact one_ne_zero),
    leviMatrix_unitary F σ hσ A, Units.ext (leviMatrix_det F σ A)⟩

variable [Finite F]

/-- The lift preserves the marked plane and has determinant one on it. -/
theorem leviSU_mem_local (A : SpecialLinearGroup (Fin 2) F) :
    leviSU F σ hσ A ∈ localFactor F (form F σ hσ) := by
  apply (mem_localFactor F _ _).mpr
  refine ⟨?_, ?_⟩
  · rw [mem_planeParabolicSU]
    simp [leviSU, leviMatrix]
  · change ( !![A 0 0,A 0 1; A 1 0,A 1 1] : Matrix (Fin 2) (Fin 2) F).det = 1
    rw [Matrix.det_fin_two]
    exact (Matrix.det_fin_two A.val).symm.trans A.property

/-- A Levi section into the published determinant-one plane local. -/
def levi : SpecialLinearGroup (Fin 2) F →* localFactor F (form F σ hσ) where
  toFun A := ⟨leviSU F σ hσ A, leviSU_mem_local F σ hσ A⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact leviMatrix_one F σ
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact leviMatrix_mul F σ A B

/-- The section has exactly the stated matrix coordinates. -/
@[simp] theorem levi_val (A : SpecialLinearGroup (Fin 2) F) :
    (levi F σ hσ A).val.val.val = leviMatrix F σ A := rfl

/-- The literal restriction map recovers the original SL₂ element. -/
@[simp] theorem factorRestriction_levi (A : SpecialLinearGroup (Fin 2) F) :
    factorRestriction F (form F σ hσ) (levi F σ hσ A) = A := by
  apply Subtype.ext
  rw [factorRestriction_val, levi_val]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem levi_injective : Function.Injective (levi F σ hσ) :=
  Function.LeftInverse.injective (factorRestriction_levi F σ hσ)

/-- Surjectivity for the exact restriction used by the radical and quotient APIs. -/
theorem factorRestriction_surjective :
    Function.Surjective (factorRestriction F (form F σ hσ)) :=
  fun A => ⟨levi F σ hσ A, factorRestriction_levi F σ hσ A⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
