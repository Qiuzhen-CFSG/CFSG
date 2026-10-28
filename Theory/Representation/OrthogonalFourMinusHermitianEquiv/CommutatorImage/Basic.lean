module

public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.OrthogonalAction

/-!
# Conjugation on the Hermitian determinant space

Entrywise field conjugation, which equals transpose on Hermitian matrices,
is an involutive quadratic isometry. It normalizes the congruence action of
SL₂ by applying the same field automorphism to its matrix coefficients.
The two diagonal singular vectors mark the hyperbolic plane used to reduce
an arbitrary isometry to an isometry of the anisotropic norm plane.

This is the concrete geometry behind the identification in Aschbacher--Smith,
Lemma I.1.6(3), printed p.408, used for the minus orthogonal block in
F.1.12(I)(6), printed p.263. No group recognition or image equality is assumed.
-/

open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open ClassicalOrthogonal.Minus (Orthogonal)

@[expose] public noncomputable section

namespace Representation.OrthogonalFourMinus.HermitianEquiv
variable (n : ℕ) [NeZero n]

/-- Entrywise conjugation on Hermitian matrices, expressed as transpose. -/
def conjugationLinear : Space n ≃ₗ[fixedField n] Space n where
  toFun X := ⟨X.val.transpose, by
    ext i j
    exact entry_conjugate n X j i⟩
  invFun X := ⟨X.val.transpose, by
    ext i j
    exact entry_conjugate n X j i⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl
  map_add' X Y := by apply Subtype.ext; rfl
  map_smul' c X := by apply Subtype.ext; rfl

@[simp] theorem conjugationLinear_val (X : Space n) :
    (conjugationLinear n X).val = X.val.transpose := rfl

/-- The conjugation involution in the full determinant-isometry group. -/
def conjugationOrthogonal : Orthogonal (fixedField n) (Space n) (form n) :=
  ⟨conjugationLinear n, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr (by
    intro X
    apply Subtype.ext
    exact Matrix.det_transpose _)⟩

@[simp] theorem conjugationOrthogonal_sq : conjugationOrthogonal n * conjugationOrthogonal n = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  rfl

theorem conjugationOrthogonal_mul_action (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) :
    conjugationOrthogonal n * orthogonalAction n A =
      orthogonalAction n (Matrix.SpecialLinearGroup.map (conjugation n).toRingHom A) *
        conjugationOrthogonal n := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change (A.val * X.val * adjoint (conjugation n) A.val).transpose =
    A.val.map (conjugation n) * X.val.transpose *
      adjoint (conjugation n) (A.val.map (conjugation n))
  have h : adjoint (conjugation n) (A.val.map (conjugation n)) = A.val.transpose := by
    ext i j
    exact conjugation_involutive n _
  rw [h, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [adjoint, Matrix.transpose_map, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The first diagonal matrix unit. -/
def firstDiagonal : Space n := (coordinates n).symm ((1, 0), 0)

/-- The second diagonal matrix unit. -/
def secondDiagonal : Space n := (coordinates n).symm ((0, 1), 0)

/-- The anisotropic norm plane, with coordinate `z` in the quadratic extension. -/
def offDiagonal : Field n →ₗ[fixedField n] Space n where
  toFun z := (coordinates n).symm ((0, 0), z)
  map_add' x y := by
    apply (coordinates n).injective
    simp
  map_smul' c z := by
    apply (coordinates n).injective
    simp

@[simp] theorem coordinates_offDiagonal (z : Field n) :
    coordinates n (offDiagonal n z) = ((0, 0), z) := by
  exact (coordinates n).apply_symm_apply _

/-- Every full quadratic isometry preserves the polar pairing. -/
theorem polar_preserved
    (g : Orthogonal (fixedField n) (Space n) (form n)) (X Y : Space n) :
    (form n).polarBilin (g.val X) (g.val Y) = (form n).polarBilin X Y := by
  have hg := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hg]

end Representation.OrthogonalFourMinus.HermitianEquiv
