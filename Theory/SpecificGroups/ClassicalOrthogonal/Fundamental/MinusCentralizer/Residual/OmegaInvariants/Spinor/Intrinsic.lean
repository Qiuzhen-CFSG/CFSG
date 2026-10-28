/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearGroups/Orthogonal/SpinorNorm.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Character
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.QuadraticWallReflectionLaw

/-!
# The intrinsic reflection-value spinor character

For a finite-dimensional nonsingular quadratic space over any field of
characteristic different from two, the determinant square class of Wall's
residual pairing is a character of the literal full orthogonal group.
Reflection generation extends the proved one-reflection law to multiplication
of arbitrary isometries. Its value on reflection in `a` is exactly `[Q a]`.

This adapts Gerald Höhn's intrinsic Wall construction to CFSG's quadratic
isometry subgroup and existing reflection-generation theorem. The separately
named `IntrinsicWall` pairing uses residual `1-g` and unhalved polar form,
so its diagonal is `Q(u)`. It does not use the differently normalized pairing
in `Theory/LinearAlgebra/QuadraticForm/Wall.lean`.

The resulting `ReflectionCharacter` also applies to every literal minus space,
including Witt index one over the field of three elements. There is no
field-size or rank bound. This discharges the existence premise of
`SpinorInvariants.mem_commutator_iff_det_character`; coordinate values and
block/scalar assembly remain separate consumers.

Sources: GLS3 §2.7, spinorial norm of a product of reflections; the orthogonal
centralizer branch of Aschbacher–Smith A.2.17, printed p.39.
Changes from ATLAS: reuse CFSG carriers and reflection APIs, public module
boundaries for Lean 4.33, and the `ReflectionCharacter`/minus-space adapters.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.IntrinsicWall
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

def wallClass (g : quadraticIsometrySubgroup Q) : Atlas.SquareClass F :=
  wallDeterminantClass Q hQ (isometryCarrierEquiv Q g)

theorem wallClass_one : wallClass Q hQ 1 = 1 := by
  let g := isometryCarrierEquiv Q (1 : quadraticIsometrySubgroup Q)
  have hr : residual Q g = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change y-y ∈ (⊥ : Submodule F V)
      simp
    · intro hx
      have hx' : x = 0 := (Submodule.mem_bot F).mp hx
      subst x
      exact ⟨0, map_zero _⟩
  have hd : Module.finrank F (residual Q g) = 0 := by rw [hr, finrank_bot]
  let : IsEmpty (Fin (Module.finrank F (residual Q g))) := by rw [hd]; infer_instance
  have he : Atlas.Bilinear.gramUnit (wallForm Q g) (wallForm_nondegenerate Q g hQ)
      (Module.finBasis F (residual Q g)) = 1 := by
    apply Units.ext
    exact Matrix.det_isEmpty
  change Atlas.squareClass F _ = 1
  rw [he, map_one]

theorem wallClass_reflection_mul (a : V) (ha : Q a ≠ 0) (g : quadraticIsometrySubgroup Q) :
    wallClass Q hQ (reflectionElement Q a ha * g) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) * wallClass Q hQ g :=
  wallDeterminantClass_reflection Q hQ (isometryCarrierEquiv Q g) a ha

theorem wallClass_reflection (a : V) (ha : Q a ≠ 0) :
    wallClass Q hQ (reflectionElement Q a ha) = Atlas.squareClass F (Units.mk0 (Q a) ha) := by
  have h := wallClass_reflection_mul Q hQ a ha 1
  rw [mul_one, wallClass_one] at h
  exact h.trans (mul_one (Atlas.squareClass F (Units.mk0 (Q a) ha)))

/-- Wall's determinant class is multiplicative in odd characteristic. -/
theorem wallClass_mul (h2 : (2 : F) ≠ 0) (g h : quadraticIsometrySubgroup Q) :
    wallClass Q hQ (g*h) = wallClass Q hQ g * wallClass Q hQ h := by
  let : CommGroup (Atlas.SquareClass F) := inferInstance
  have hg : g ∈ reflectionSubgroup Q := by rw [reflectionSubgroup_eq_top Q hQ h2]; trivial
  have hall : ∀ k : quadraticIsometrySubgroup Q, k ∈ reflectionSubgroup Q →
      ∀ t, wallClass Q hQ (k*t) = wallClass Q hQ k * wallClass Q hQ t := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨a, ha, rfl⟩ := hk
      intro t
      rw [wallClass_reflection_mul, wallClass_reflection]
    | one =>
      intro t
      rw [one_mul, wallClass_one]
      exact (one_mul (wallClass Q hQ t)).symm
    | mul x y hx hy ihx ihy =>
      intro t
      rw [mul_assoc, ihx, ihy, ihx, mul_assoc]
    | inv x hx ih =>
      intro t
      apply mul_left_cancel (a := wallClass Q hQ x)
      rw [← ih, mul_inv_cancel_left, ← mul_assoc, ← ih, mul_inv_cancel,
        wallClass_one, one_mul]
  exact hall g hg h

/-- The intrinsic spinor norm, defined by the determinant class of Wall's residual form. -/
def spinorNorm (h2 : (2 : F) ≠ 0) : quadraticIsometrySubgroup Q →* Atlas.SquareClass F where
  toFun := wallClass Q hQ
  map_one' := wallClass_one Q hQ
  map_mul' := wallClass_mul Q hQ h2

@[simp] theorem spinorNorm_reflection (h2 : (2 : F) ≠ 0) (a : V) (ha : Q a ≠ 0) :
    spinorNorm Q hQ h2 (reflectionElement Q a ha) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) := wallClass_reflection Q hQ a ha

end ClassicalOrthogonal.IntrinsicWall


namespace ClassicalOrthogonal.SpinorInvariants
open ClassicalOrthogonal.ReflectionGeneration
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- The intrinsic spinor character exists over any field of characteristic
other than two, with no finiteness or Witt-index assumption. -/
def intrinsicReflectionCharacter (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0) : ReflectionCharacter Q where
  hom := IntrinsicWall.spinorNorm Q hQ h2
  reflection_value := IntrinsicWall.spinorNorm_reflection Q hQ h2

/-- Reflection values for the constructed homomorphism on the literal carrier. -/
@[simp] theorem intrinsicReflectionCharacter_reflection (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0) (a : V) (ha : Q a ≠ 0) :
    (intrinsicReflectionCharacter Q hQ h2).hom (reflectionElement Q a ha) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) :=
  (intrinsicReflectionCharacter Q hQ h2).reflection_value a ha

/-- The existence assertion, with all construction premises discharged. -/
theorem nonempty_reflectionCharacter (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0) :
    Nonempty (ReflectionCharacter Q) := ⟨intrinsicReflectionCharacter Q hQ h2⟩

variable (F) [Finite F]

/-- The character on `Minus.Space F r`, using its proved nonsingularity.
This includes `r = 1` and every odd finite field, including `ZMod 3`. -/
def minusReflectionCharacter (r : ℕ) (h2 : (2 : F) ≠ 0) :
    ReflectionCharacter (Minus.quadraticForm F (r + 1)) :=
  intrinsicReflectionCharacter _ (Minus.quadraticForm_nonsingular F (r + 1)) h2

@[simp] theorem minusReflectionCharacter_reflection (r : ℕ) (h2 : (2 : F) ≠ 0)
    (a : Minus.Space F r) (ha : Minus.quadraticForm F (r + 1) a ≠ 0) :
    (minusReflectionCharacter F r h2).hom
      (reflectionElement (Minus.quadraticForm F (r + 1)) a ha) =
        Atlas.squareClass F (Units.mk0 (Minus.quadraticForm F (r + 1) a) ha) :=
  (minusReflectionCharacter F r h2).reflection_value a ha

end ClassicalOrthogonal.SpinorInvariants
