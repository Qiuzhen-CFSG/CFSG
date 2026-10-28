module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Coordinates
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases

/-!
# Matrices for the five-dimensional unitary line radical

The coordinate group has a faithful upper triangular matrix representation
in a Witt basis. Its matrices have determinant one and preserve the Gram
matrix with a hyperbolic pair surrounding an identity three-space.
A trace-one scalar gives an explicit change of basis from this Witt form to
the identity form, with the first basis vector spanning the chosen line.
Identification of the full parabolic kernel is a separate step.

Source: the unitary line-parabolic calculation used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

def wittGram : Matrix (Fin 5) (Fin 5) F :=
  !![0,0,0,0,1; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 1,0,0,0,0]

def unipotentMatrix (x : Coord J) : Matrix (Fin 5) (Fin 5) F :=
  !![1,J.conj (x.vector 0),J.conj (x.vector 1),J.conj (x.vector 2),x.scalar;
     0,1,0,0,x.vector 0;
     0,0,1,0,x.vector 1;
     0,0,0,1,x.vector 2;
     0,0,0,0,1]

@[simp] theorem unipotentMatrix_one : unipotentMatrix J 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentMatrix]

theorem unipotentMatrix_mul (x y : Coord J) :
    unipotentMatrix J (x * y) = unipotentMatrix J x * unipotentMatrix J y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentMatrix, Matrix.mul_apply, Fin.sum_univ_succ, pairing] <;> ring

theorem unipotentMatrix_injective : Function.Injective (unipotentMatrix J) := by
  intro x y h
  apply Coord.ext
  · ext i
    fin_cases i
    · exact congrArg (fun A => A 1 4) h
    · exact congrArg (fun A => A 2 4) h
    · exact congrArg (fun A => A 3 4) h
  · exact congrArg (fun A => A 0 4) h

theorem unipotentMatrix_det (x : Coord J) : (unipotentMatrix J x).det = 1 := by
  have hu : (unipotentMatrix J x).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [unipotentMatrix]
  rw [Matrix.det_of_isUpperTriangular hu]
  simp [Fin.prod_univ_succ, unipotentMatrix]

variable [CharP F 2]

theorem unipotentMatrix_preserves (x : Coord J) :
    J.conjTranspose (unipotentMatrix J x) * wittGram * unipotentMatrix J x = wittGram := by
  have hσ (a : F) := J.conj_involutive a
  have hx := x.trace_eq
  simp [pairing, Fin.sum_univ_succ] at hx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, unipotentMatrix, wittGram,
      Matrix.mul_apply, Fin.sum_univ_succ, hσ, CharTwo.add_self_eq_zero]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination hx + (J.conj (x.vector 0) * x.vector 0 +
    J.conj (x.vector 1) * x.vector 1 + J.conj (x.vector 2) * x.vector 2) * h2

/-- A faithful matrix representation of the radical coordinates. -/
def unipotentGL : Coord J →* GL (Fin 5) F where
  toFun x := ⟨unipotentMatrix J x, unipotentMatrix J x⁻¹,
    by rw [← unipotentMatrix_mul, mul_inv_cancel, unipotentMatrix_one],
    by rw [← unipotentMatrix_mul, inv_mul_cancel, unipotentMatrix_one]⟩
  map_one' := Units.ext (unipotentMatrix_one J)
  map_mul' x y := Units.ext (unipotentMatrix_mul J x y)

theorem unipotentGL_injective : Function.Injective (unipotentGL J) := by
  intro x y h
  exact unipotentMatrix_injective J (congrArg Units.val h)

/-- Columns are the given isotropic line, three orthonormal vectors, and its partner. -/
def wittBasisMatrix (c : F) : Matrix (Fin 5) (Fin 5) F :=
  !![1,0,0,0,c; 1,0,0,0,1+c; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0]

def wittBasisInverse (c : F) : Matrix (Fin 5) (Fin 5) F :=
  !![1+c,c,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1; 1,1,0,0,0]

theorem wittBasis_mul_inverse (c : F) : wittBasisMatrix c * wittBasisInverse c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittBasisMatrix, wittBasisInverse, Matrix.mul_apply,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals simp [CharTwo.two_eq_zero]

theorem wittBasis_inverse_mul (c : F) : wittBasisInverse c * wittBasisMatrix c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittBasisMatrix, wittBasisInverse, Matrix.mul_apply,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals simp [CharTwo.two_eq_zero]

def wittBasisGL (c : F) : GL (Fin 5) F :=
  ⟨wittBasisMatrix c, wittBasisInverse c, wittBasis_mul_inverse c, wittBasis_inverse_mul c⟩

theorem wittBasis_gram (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    J.conjTranspose (wittBasisMatrix c) * J.form * wittBasisMatrix c = wittGram := by
  rw [hJ, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittBasisMatrix, wittGram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination hc + h2

end Theory.SpecificGroups.UnitaryFive.LineCore
