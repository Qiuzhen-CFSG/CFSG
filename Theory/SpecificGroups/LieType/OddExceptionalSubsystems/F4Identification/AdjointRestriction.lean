module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Curves

/-!
# Backward word relations from the concrete adjoint restriction

The orbit-sum matrix intertwines whole words whenever it intertwines the
eight signed simple-root curves: multiplication and inversion preserve the
matrix identity. If the restriction is injective, a folded word equal to
the identity therefore has identity F4-cover value, which supplies the
backward central-word premise of `evaluationKernels_eq_of_relations`.

The final two theorems assemble this implication from two precisely stated
obligations on the concrete map: lifting every F4 root and the integral
polynomial generator identities. These obligations are still explicit;
this module does not yet prove the unconditional backward word implication.

Sources: Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`, and
GLS3 §§2.2--2.6. All matrix actions below use column vectors.
-/

public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
open Theory.AlgebraicGroup.StandardRootSystem Matrix
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

private theorem inverse_intertwines {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : (Matrix m m R)ˣ) (B : (Matrix n n R)ˣ) (J : Matrix n m R)
    (h : B.val * J = J * A.val) :
    B⁻¹.val * J = J * A⁻¹.val := by
  calc
    B⁻¹.val * J = B⁻¹.val * (J * A.val) * A⁻¹.val := by
      simp [Matrix.mul_assoc]
    _ = B⁻¹.val * (B.val * J) * A⁻¹.val := by rw [h]
    _ = J * A⁻¹.val := by simp [← Matrix.mul_assoc]

/-- Generator identities propagate to the actual two free-word evaluations, including inverses. -/
theorem word_intertwines
    (h : ∀ s i t, foldedCurve F s i t * matrix F = matrix F * sourceCurve F s i t)
    (w : Word F) :
    (foldedEvaluation F w).val.val.val * matrix F =
      matrix F * (coverEvaluation F w).val.val := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of x =>
    obtain ⟨s, i, t⟩ := x
    simpa [sourceCurve] using h s i t
  | inv_of x ih =>
    simpa only [map_inv, Subgroup.coe_inv] using
      inverse_intertwines (coverEvaluation F (FreeGroup.of x)).val
        (foldedEvaluation F (FreeGroup.of x)).val.val (matrix F) ih
  | mul x y hx hy =>
    simp only [map_mul, Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]

/-- Faithful restriction of the column action gives the stronger backward word implication. -/
theorem coverEvaluation_eq_one_of_injective_of_curves
    (hinj : Function.Injective (linearMap F))
    (h : ∀ s i t, foldedCurve F s i t * matrix F = matrix F * sourceCurve F s i t)
    (w : Word F) (hw : foldedEvaluation F w = 1) : coverEvaluation F w = 1 := by
  have he := word_intertwines F h w
  rw [hw] at he
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mul] at he
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  funext x
  apply hinj
  change matrix F *ᵥ ((coverEvaluation F w).val.val *ᵥ x) = matrix F *ᵥ ((1 : Matrix SourceIndex SourceIndex F) *ᵥ x)
  rw [Matrix.mulVec_mulVec, ← he, Matrix.one_mulVec]

/-- Assembly from two independent integral/root-geometric obligations.
The hypotheses here are not asserted by this module. -/
theorem coverEvaluation_eq_one_of_root_lifts_of_integral_polynomial
    (hlift : ∀ s : typeF4Roots, ∃ r : typeE6Roots, rootProjection r.val = s.val)
    (hpoly : ∀ s i,
      foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
        matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X)
    (w : Word F) (hw : foldedEvaluation F w = 1) : coverEvaluation F w = 1 :=
  coverEvaluation_eq_one_of_injective_of_curves F
    (linearMap_injective_of_root_lifts F hlift)
    (curve_intertwines_of_integral_polynomial F hpoly) w hw

/-- The exact backward premise of the parent's evaluation-kernel assembly. -/
theorem coverEvaluation_central_of_root_lifts_of_integral_polynomial
    (hlift : ∀ s : typeF4Roots, ∃ r : typeE6Roots, rootProjection r.val = s.val)
    (hpoly : ∀ s i,
      foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
        matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X)
    (w : Word F) (hw : foldedEvaluation F w = 1) :
    coverEvaluation F w ∈ Subgroup.center (Cover F) := by
  rw [coverEvaluation_eq_one_of_root_lifts_of_integral_polynomial F hlift hpoly w hw]
  exact Subgroup.one_mem _

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
