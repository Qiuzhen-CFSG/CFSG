module

public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Orthogonal-frame tori in the actual SU₃ and PSU₃ groups

An orthogonal frame is an invertible basis matrix whose Hermitian Gram matrix
is the identity. Its special torus consists of the determinant-one unitary
matrices diagonal in that frame. The projective torus is its image under the
actual SU₃-to-PSU₃ map, so the scalar kernel is retained.

The two tori are abelian, by injection into the group of diagonal matrices
and then passage to the projective image. Their orders, full normalizers,
and placement of arbitrary odd subgroups are not part of these definitions.

Source: GLS, Volume 4, Chapter 4, Lemma 3.11
(`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603); orthonormal bases are
constructed in Huppert II.10.4(a).
-/

@[expose] public section

open Matrix Subgroup

namespace UnitaryThree.OddTorusNormalizer
open BenderSuzuki.MatrixGroups
variable {E : Type*} [Field E]

/-- An actual change of basis taking the Hermitian form to the identity. -/
abbrev OrthogonalFrame (J : HermitianForm 3 E) :=
  {P : GL (Fin 3) E // J.conjTranspose P.val * J.form * P.val = 1}

/-- The usual embedding of diagonal field units into GL₃. -/
def diagonalHom : (Fin 3 → Eˣ) →* GL (Fin 3) E where
  toFun a :=
    { val := Matrix.diagonal (fun i => (a i : E))
      inv := Matrix.diagonal (fun i => ((a i)⁻¹ : Eˣ))
      val_inv := by simp [Matrix.diagonal_mul_diagonal]
      inv_val := by simp [Matrix.diagonal_mul_diagonal] }
  map_one' := by
    apply Units.ext
    exact Matrix.diagonal_one
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.diagonal_mul_diagonal]
    rfl

/-- The diagonal subgroup in SU₃, expressed in the chosen orthogonal frame. -/
def specialFrameTorus (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Subgroup J.specialSubgroup :=
  diagonalHom.range.comap
    ((MulAut.conj P.val⁻¹).toMonoidHom.comp J.specialSubgroup.subtype)

/-- Its image in the literal projective special unitary group. -/
def projectiveFrameTorus (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (specialFrameTorus J P).map J.specialToProjective

instance specialFrameTorus_commutative (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    IsMulCommutative (specialFrameTorus J P) := by
  apply Subgroup.comap_injective_isMulCommutative
  exact (MulAut.conj P.val⁻¹).injective.comp J.specialSubgroup.subtype_injective

instance projectiveFrameTorus_commutative (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    IsMulCommutative (projectiveFrameTorus J P) := by
  unfold projectiveFrameTorus
  infer_instance

end UnitaryThree.OddTorusNormalizer
