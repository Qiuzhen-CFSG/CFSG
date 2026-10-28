module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
import Mathlib.Tactic.FinCases

/-!
# Reference bases for the two isotropic subspace dimensions

The first coordinate axis and the plane on the first and third axes map
onto the prescribed unitary-five line and plane. The explicit reference
matrices are involutions in characteristic two. Their Gram matrices have
one or two blocks `!![0,1;1,1]`, with identity matrix on the complement.
Thus the second vector of each hyperbolic pair has norm one.

`HasAdaptedBasis` specifies an actual invertible basis with this precise
Gram matrix and subspace image. It is an existence contract, not an assertion
that such a basis has been constructed for every isotropic subspace.

Source: Hermitian adapted bases and Witt extension, GLS3, Lemma 2.7.1,
printed p.89, in `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
variable {F : Type*} [Field F]

/-- The first coordinate axis, or the plane on the first and third axes. -/
def coordinateSubspace (F : Type*) [Field F] (b : Bool) : Submodule F (Fin 5 → F) where
  carrier := {v | v 1 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ (b = false → v 2 = 0)}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨h1,h3,h4,h2⟩ ⟨k1,k3,k4,k2⟩; simp_all
  smul_mem' := by rintro a v ⟨h1,h3,h4,h2⟩; simp_all

/-- A fixed basis carrying the coordinate axis or plane onto the standard flag. -/
def referenceMatrix (b : Bool) : Matrix (Fin 5) (Fin 5) F :=
  if b then
    !![1,0,0,0,0; 1,1,0,0,0; 0,0,1,0,0; 0,0,1,1,0; 0,0,0,0,1]
  else
    !![1,0,0,0,0; 1,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1]

/-- Gram matrix with one or two hyperbolic pairs. The second vector in each
pair has norm one; the remaining coordinates have identity Gram matrix. -/
def referenceGram (b : Bool) : Matrix (Fin 5) (Fin 5) F :=
  if b then
    !![0,1,0,0,0; 1,1,0,0,0; 0,0,0,1,0; 0,0,1,1,0; 0,0,0,0,1]
  else
    !![0,1,0,0,0; 1,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1]

/-- An actual invertible adapted basis, including its Gram matrix and subspace image. -/
def HasAdaptedBasis (J : HermitianForm 5 F) (b : Bool)
    (W : Submodule F (Fin 5 → F)) : Prop :=
  ∃ P : GL (Fin 5) F, J.conjTranspose P.val * P.val = referenceGram b ∧
    W = (coordinateSubspace F b).map P.val.mulVecLin

variable [CharP F 2]

theorem referenceMatrix_sq (b : Bool) :
    (referenceMatrix b : Matrix (Fin 5) (Fin 5) F) * referenceMatrix b = 1 := by
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [referenceMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      CharTwo.add_self_eq_zero]

def referenceGL (b : Bool) : GL (Fin 5) F :=
  ⟨referenceMatrix b, referenceMatrix b, referenceMatrix_sq b, referenceMatrix_sq b⟩

theorem referenceMatrix_gram (J : HermitianForm 5 F) (b : Bool) :
    J.conjTranspose (referenceMatrix b) * referenceMatrix b = referenceGram b := by
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [referenceMatrix, referenceGram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
private theorem referenceMatrix_mem_iff (b : Bool) (v : Fin 5 → F) :
    referenceMatrix b *ᵥ v ∈ (if b then plane F else line F) ↔
      v ∈ coordinateSubspace F b := by
  cases b <;>
    simp [referenceMatrix, line, plane, coordinateSubspace, dotProduct,
      Fin.sum_univ_succ]
  · aesop

/-- The reference basis maps the coordinate subspace to the actual standard flag. -/
theorem referenceMatrix_map (b : Bool) :
    (coordinateSubspace F b).map (referenceMatrix b).mulVecLin =
      (if b then plane F else line F) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (referenceMatrix_mem_iff b w).mpr hw
  · intro hv
    have he : referenceMatrix b *ᵥ (referenceMatrix b *ᵥ v) = v := by
      rw [mulVec_mulVec, referenceMatrix_sq, one_mulVec]
    refine ⟨referenceMatrix b *ᵥ v, ?_, he⟩
    exact (referenceMatrix_mem_iff b _).mp (he.symm ▸ hv)

end Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
