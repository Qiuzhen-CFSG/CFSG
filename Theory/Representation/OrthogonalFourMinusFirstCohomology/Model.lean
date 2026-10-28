module

public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.Abel

/-!
# The Hermitian matrix model for the four-dimensional minus module

For a field automorphism `σ`, determinant-one two-by-two matrices act on the
full matrix space by `X ↦ A X (σ(A))ᵀ`. This is the tensor product of the natural
representation with its coefficient twist. For an involutive automorphism
fixing the coefficient field, Hermitian matrices form a subrepresentation.
The action preserves determinant, and a Hermitian matrix has fixed determinant.

The final lemma descends principal cocycles from the full matrix space: if the
ambient action has no fixed vectors, its principal vector is unique, so
conjugate transposition fixes that vector. The finite-field geometry and the
ambient cohomology calculation are separate results; neither is assumed here
as a property of an unnamed orthogonal module.

This is the matrix construction used for the four-dimensional orthogonal
module in Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408. The proofs in this
module are characteristic-free matrix identities and an elementary descent
argument for the explicit cocycle quotient.
-/

@[expose] public section

namespace Representation.OrthogonalFourMinus

variable {F : Type*} [Field F]

/-- The ambient two-by-two matrix space. -/
abbrev Mat (F : Type*) := Matrix (Fin 2) (Fin 2) F

/-- Transpose followed by the specified coefficient automorphism. -/
def adjoint (σ : F ≃+* F) (X : Mat F) : Mat F := X.transpose.map σ

lemma adjoint_add (σ : F ≃+* F) (X Y : Mat F) :
    adjoint σ (X + Y) = adjoint σ X + adjoint σ Y := by
  ext i j
  exact map_add σ _ _

lemma adjoint_sub (σ : F ≃+* F) (X Y : Mat F) :
    adjoint σ (X - Y) = adjoint σ X - adjoint σ Y := by
  ext i j
  exact map_sub σ _ _

lemma adjoint_mul (σ : F ≃+* F) (X Y : Mat F) :
    adjoint σ (X * Y) = adjoint σ Y * adjoint σ X := by
  simp only [adjoint, Matrix.transpose_mul, Matrix.map_mul]

lemma adjoint_one (σ : F ≃+* F) : adjoint σ (1 : Mat F) = 1 := by
  simp [adjoint]

lemma adjoint_involutive (σ : F ≃+* F) (hσ : Function.Involutive σ) :
    Function.Involutive (adjoint σ) := by
  intro X
  ext i j
  exact hσ (X i j)

/-- The tensor of the natural action and its coefficient twist, realized on matrices. -/
def tensorAction (σ : F ≃+* F) :
    Representation F (Matrix.SpecialLinearGroup (Fin 2) F) (Mat F) where
  toFun A := {
    toFun := fun X => A.val * X * adjoint σ A.val
    map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intro c X; simp }
  map_one' := by ext X i j; simp [adjoint_one]
  map_mul' A B := by
    ext X i j
    change ((A * B).val * X * adjoint σ (A * B).val) i j =
      (A.val * (B.val * X * adjoint σ B.val) * adjoint σ A.val) i j
    rw [Matrix.SpecialLinearGroup.coe_mul, adjoint_mul]
    simp only [Matrix.mul_assoc]

lemma tensorAction_apply (σ : F ≃+* F)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (X : Mat F) :
    tensorAction σ A X = A.val * X * adjoint σ A.val := rfl

lemma adjoint_tensorAction (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (X : Mat F) :
    adjoint σ (tensorAction σ A X) = tensorAction σ A (adjoint σ X) := by
  rw [tensorAction_apply, adjoint_mul, adjoint_mul, adjoint_involutive σ hσ,
    tensorAction_apply, Matrix.mul_assoc]

lemma det_adjoint (σ : F ≃+* F) (X : Mat F) :
    (adjoint σ X).det = σ X.det := by
  change (σ.mapMatrix X.transpose).det = σ X.det
  rw [← σ.map_det, Matrix.det_transpose]

lemma det_tensorAction (σ : F ≃+* F)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (X : Mat F) :
    (tensorAction σ A X).det = X.det := by
  rw [tensorAction_apply, Matrix.det_mul, Matrix.det_mul]
  have hdet : (adjoint σ A.val).det = 1 := by
    rw [det_adjoint, A.property, map_one]
  rw [A.property, hdet, one_mul, mul_one]

section Hermitian
variable {k : Type*} [Field k] [Algebra k F]

/-- Hermitian matrices form a subrepresentation over the fixed coefficient field. -/
def hermitian (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ) :
    Subrepresentation (restrictScalars (k := k) (tensorAction σ.toRingEquiv)) where
  toSubmodule := {
    carrier := {X | adjoint σ.toRingEquiv X = X}
    zero_mem' := by ext i j; exact map_zero σ
    add_mem' := by
      intro X Y hX hY
      change adjoint σ.toRingEquiv (X + Y) = X + Y
      have h : adjoint σ.toRingEquiv (X + Y) =
          adjoint σ.toRingEquiv X + adjoint σ.toRingEquiv Y := by
        ext i j; exact map_add σ _ _
      rw [h, hX, hY]
    smul_mem' := by
      intro c X hX
      change adjoint σ.toRingEquiv (c • X) = c • X
      have h : adjoint σ.toRingEquiv (c • X) = c • adjoint σ.toRingEquiv X := by
        ext i j; exact σ.toLinearMap.map_smul c (X j i)
      rw [h, hX] }
  apply_mem_toSubmodule := by
    intro A X hX
    change adjoint σ.toRingEquiv
      (A.val * X * adjoint σ.toRingEquiv A.val) =
      A.val * X * adjoint σ.toRingEquiv A.val
    rw [adjoint_mul, adjoint_mul, adjoint_involutive σ.toRingEquiv hσ, hX]
    exact (Matrix.mul_assoc _ _ _).symm

/-- The action on Hermitian matrices; over a quadratic finite-field extension
this realizes the natural four-dimensional minus-type orthogonal module. -/
def hermitianAction (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ) :=
  (hermitian σ hσ).toRepresentation

lemma hermitianAction_apply (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (X : hermitian σ hσ) :
    (hermitianAction σ hσ A X).val = A.val * X.val * adjoint σ.toRingEquiv A.val := rfl

lemma det_hermitianAction (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (X : hermitian σ hσ) :
    (hermitianAction σ hσ A X).val.det = X.val.det :=
  det_tensorAction σ.toRingEquiv A X.val

/-- A Hermitian matrix has determinant fixed by conjugation. -/
lemma det_fixed (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)
    (X : hermitian σ hσ) : σ X.val.det = X.val.det := by
  change σ.toRingEquiv X.val.det = X.val.det
  rw [← det_adjoint σ.toRingEquiv, X.property]

/-- Descent of principal cocycles from the full twisted tensor module.
Uniqueness of a principal vector forces it to be Hermitian. -/
lemma principal_surjective_of_tensor (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)
    (hfixed : OneCohomology.fixed (tensorAction σ.toRingEquiv) = ⊥)
    (hprincipal : Function.Surjective (OneCohomology.principal (tensorAction σ.toRingEquiv))) :
    Function.Surjective (OneCohomology.principal (hermitianAction σ hσ)) := by
  intro f
  let f' : OneCohomology.cocycles (tensorAction σ.toRingEquiv) :=
    ⟨fun A => (f.val A).val, fun A B => congrArg Subtype.val (f.property A B)⟩
  obtain ⟨X, hX⟩ := hprincipal f'
  have he (A : Matrix.SpecialLinearGroup (Fin 2) F) :
      tensorAction σ.toRingEquiv A X - X = (f.val A).val :=
    congrArg (fun c : OneCohomology.cocycles (tensorAction σ.toRingEquiv) => c.val A) hX
  have hJ : adjoint σ.toRingEquiv X - X ∈
      OneCohomology.fixed (tensorAction σ.toRingEquiv) := by
    intro A
    have h := congrArg (adjoint σ.toRingEquiv) (he A)
    rw [adjoint_sub, adjoint_tensorAction σ.toRingEquiv hσ, (f.val A).property] at h
    rw [map_sub]
    have heA := he A
    calc
      tensorAction σ.toRingEquiv A (adjoint σ.toRingEquiv X) -
          tensorAction σ.toRingEquiv A X =
        (tensorAction σ.toRingEquiv A (adjoint σ.toRingEquiv X) - adjoint σ.toRingEquiv X) -
          (tensorAction σ.toRingEquiv A X - X) + (adjoint σ.toRingEquiv X - X) := by abel
      _ = adjoint σ.toRingEquiv X - X := by rw [h, heA]; abel
  rw [hfixed, Submodule.mem_bot] at hJ
  refine ⟨⟨X, sub_eq_zero.mp hJ⟩, ?_⟩
  apply Subtype.ext
  funext A
  apply Subtype.ext
  exact he A

end Hermitian

end Representation.OrthogonalFourMinus
