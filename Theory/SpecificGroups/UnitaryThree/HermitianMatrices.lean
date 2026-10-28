module

public import Theory.SpecificGroups.UnitaryThree.PermutationModel
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Explicit Hermitian matrices for the degree-28 unitary model

The root, torus and swapping matrices have determinant one and preserve the
anti-diagonal Hermitian Gram matrix `gram`. The columns of `basisMatrix` form
an isotropic basis for the identity form: `basisMatrixᴴ * basisMatrix = gram`.
Its determinant is `1 + i`, so conjugating by this basis carries every isometry
of `gram` to an isometry of the identity form. Thus the change of form needed
by the projective identification is explicit.

The finite matrix identities are checked by kernel reduction. This module
makes no assertion yet that the generated permutation group is the full
projective unitary group.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections IV and VI. The basis change is a direct calculation over F₃[i].
-/

@[expose] public section

open FiniteField Matrix
open scoped Matrix
namespace UnitaryThree

def gram : Matrix (Fin 3) (Fin 3) Nine := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

def rootMatrix (p : Root) : SpecialLinearGroup (Fin 3) Nine :=
  ⟨!![1, -star p.val.1, p.val.2; 0, 1, p.val.1; 0, 0, 1], by
    simp [Matrix.det_fin_three]⟩

def torusMatrix (r : Nineˣ) : SpecialLinearGroup (Fin 3) Nine :=
  ⟨!![(r : Nine) ^ 5, 0, 0; 0, (r : Nine) ^ 2, 0; 0, 0, (r : Nine)], by
    have h : ∀ r : Nineˣ,
        (!![(r : Nine) ^ 5, 0, 0; 0, (r : Nine) ^ 2, 0; 0, 0, (r : Nine)]).det = 1 := by
      decide +kernel
    exact h r⟩

def swapMatrix : SpecialLinearGroup (Fin 3) Nine := ⟨-gram, by decide⟩

theorem rootMatrix_isometry (p : Root) :
    (rootMatrix p).valᴴ * gram * (rootMatrix p).val = gram := by
  have h : ∀ p : Root, (rootMatrix p).valᴴ * gram * (rootMatrix p).val = gram := by
    decide +kernel
  exact h p

theorem torusMatrix_isometry (r : Nineˣ) :
    (torusMatrix r).valᴴ * gram * (torusMatrix r).val = gram := by
  have h : ∀ r : Nineˣ, (torusMatrix r).valᴴ * gram * (torusMatrix r).val = gram := by
    decide +kernel
  exact h r

theorem swapMatrix_isometry : swapMatrix.valᴴ * gram * swapMatrix.val = gram := by decide

def basisMatrix : Matrix (Fin 3) (Fin 3) Nine :=
  !![1, ⟨1, 1⟩, 1; 1, ⟨2, 2⟩, 1; 1, 0, 2]

theorem basisMatrix_gram : basisMatrixᴴ * basisMatrix = gram := by decide

theorem basisMatrix_det : basisMatrix.det = (⟨1, 1⟩ : Nine) := by decide

def basisGL : GL (Fin 3) Nine :=
  GeneralLinearGroup.mkOfDetNeZero basisMatrix (by rw [basisMatrix_det]; decide)


theorem basisGL_coe : (basisGL : Matrix (Fin 3) (Fin 3) Nine) = basisMatrix := by rfl

theorem change_form_isometry (A : Matrix (Fin 3) (Fin 3) Nine)
    (hA : Aᴴ * gram * A = gram) :
    (basisMatrix * A * ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine))ᴴ *
      (basisMatrix * A * ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine)) = 1 := by
  have hcancel := Units.mul_inv basisGL
  rw [basisGL_coe] at hcancel
  calc
    _ = ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine)ᴴ *
        (Aᴴ * (basisMatrixᴴ * basisMatrix) * A) *
          ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine)ᴴ * gram *
        ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine) := by rw [basisMatrix_gram, hA]
    _ = (basisMatrix * ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine))ᴴ *
        (basisMatrix * ((basisGL⁻¹ : GL (Fin 3) Nine) : Matrix (Fin 3) (Fin 3) Nine)) := by
      rw [← basisMatrix_gram]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hcancel]; simp

end UnitaryThree

end
