module

public import Theory.Representation.GLTwoBorel
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# Weyl-invariant Borel representations extend through the determinant

The diagonal torus is embedded in the existing concrete Borel. A Borel
representation trivial on upper unipotents is determined by its diagonal
values. If its two diagonal restrictions agree, these values depend only on
the determinant; composing the first restriction with determinant extends it.
This is the exceptional-character step in the GL₂ principal-series argument
used with Brauer, Desarguesian planes II, printed p. 128. No finiteness or
characteristic restriction is needed for this step.
-/

open scoped MatrixGroups

namespace GLTwo

variable {F : Type*} [Field F]

@[expose] public def borelDiagonal (first second : Fˣ) : borelSubgroup F :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(first : F), 0; 0, (second : F)] (by simp [Matrix.det_fin_two]), by simp⟩

@[simp] public theorem borelDiagonal_mul (first second third fourth : Fˣ) :
    borelDiagonal first second * borelDiagonal third fourth =
      borelDiagonal (first * third) (second * fourth) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [borelDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] public theorem borelDiagonal_one : borelDiagonal (1 : Fˣ) 1 = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [borelDiagonal]

@[expose] public def borelFirstDiagonal : Fˣ →* borelSubgroup F where
  toFun first := borelDiagonal first 1
  map_one' := borelDiagonal_one
  map_mul' first second := by simp

private theorem diagonal_nonzero (matrix : borelSubgroup F) :
    matrix.val 0 0 ≠ 0 ∧ matrix.val 1 1 ≠ 0 := by
  have hdet := matrix.val.det_ne_zero
  have hlower := (mem_borelSubgroup F matrix.val).mp matrix.property
  simpa [Matrix.det_fin_two, hlower, mul_ne_zero_iff] using hdet

private theorem diagonal_unipotent_factorization (matrix : borelSubgroup F) :
    matrix = borelDiagonal
        (Units.mk0 (matrix.val 0 0) (diagonal_nonzero matrix).1)
        (Units.mk0 (matrix.val 1 1) (diagonal_nonzero matrix).2) *
      upperUnipotent F (matrix.val 0 1 / matrix.val 0 0) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [borelDiagonal, upperUnipotent, Matrix.GeneralLinearGroup.upperRightHom,
      Matrix.mul_apply, Fin.sum_univ_two,
      (mem_borelSubgroup F matrix.val).mp matrix.property]
  field_simp [(diagonal_nonzero matrix).1]

public theorem borel_representation_eq_determinant
    (tau : Representation ℂ (borelSubgroup F) ℂ)
    (htrivial : ∀ parameter : F, tau (upperUnipotent F parameter) = 1)
    (hequal : ∀ unit : Fˣ, tau (borelDiagonal unit 1) = tau (borelDiagonal 1 unit))
    (matrix : borelSubgroup F) :
    tau matrix = tau (borelDiagonal (Matrix.GeneralLinearGroup.det matrix.val) 1) := by
  let first := Units.mk0 (matrix.val 0 0) (diagonal_nonzero matrix).1
  let second := Units.mk0 (matrix.val 1 1) (diagonal_nonzero matrix).2
  have hfactor : matrix = borelDiagonal first second *
      upperUnipotent F (matrix.val 0 1 / matrix.val 0 0) :=
    diagonal_unipotent_factorization matrix
  have hdet : Matrix.GeneralLinearGroup.det matrix.val = first * second := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
      (mem_borelSubgroup F matrix.val).mp matrix.property, first, second]
  calc
    tau matrix = tau (borelDiagonal first second) := by rw [hfactor, map_mul, htrivial, mul_one]
    _ = tau (borelDiagonal first 1) * tau (borelDiagonal 1 second) := by
      rw [← map_mul, borelDiagonal_mul, mul_one, one_mul]
    _ = tau (borelDiagonal first 1) * tau (borelDiagonal second 1) := by rw [← hequal]
    _ = tau (borelDiagonal (Matrix.GeneralLinearGroup.det matrix.val) 1) := by
      rw [← map_mul, borelDiagonal_mul, one_mul, hdet]

public theorem borel_representation_extends_of_diagonal_eq
    (tau : Representation ℂ (borelSubgroup F) ℂ)
    (htrivial : ∀ parameter : F, tau (upperUnipotent F parameter) = 1)
    (hequal : ∀ unit : Fˣ, tau (borelDiagonal unit 1) = tau (borelDiagonal 1 unit)) :
    ∃ line : Representation ℂ (GL (Fin 2) F) ℂ,
      line.comp (borelSubgroup F).subtype = tau := by
  refine ⟨(tau.comp borelFirstDiagonal).comp Matrix.GeneralLinearGroup.det, ?_⟩
  apply MonoidHom.ext
  intro matrix
  exact (borel_representation_eq_determinant tau htrivial hequal matrix).symm

end GLTwo
