/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/QuadraticResidualReflection.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and a separate IntrinsicWall namespace for the residual 1-g normalization.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.QuadraticResidual
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Residual restriction after an anisotropic reflection in the residual space

Reflecting in an anisotropic residual vector projects the residual onto
its right Wall-perpendicular complement. The explicit projection identifies
the new Wall form with the restriction of the old one, supplying the
one-dimensional determinant factorization.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace ClassicalOrthogonal.IntrinsicWall
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (g : Q.IsometryEquiv Q)

/-- Wall's reversed residual formula. -/
theorem wallForm_residual_right (u : residual Q g) (x : V) :
    wallForm Q g u ((residualMap Q g).rangeRestrict x) = -Q.polarBilin (g x) u.val := by
  have h := wallForm_symmetrization Q g u ((residualMap Q g).rangeRestrict x)
  rw [wallForm_residual] at h
  change wallForm Q g u ((residualMap Q g).rangeRestrict x) + Q.polarBilin x u.val =
    Q.polarBilin u.val (x-g x) at h
  rw [map_sub, polar_swap Q u.val x, polar_swap Q u.val (g x)] at h
  linear_combination h

def reflectedIsometry (a : V) (ha : Q a ≠ 0) : Q.IsometryEquiv Q :=
  g.trans (reflectionIsometry Q a ha)

theorem reflected_residual (a : V) (ha : Q a ≠ 0) (x : V) :
    residualMap Q (reflectedIsometry Q g a ha) x =
      residualMap Q g x + ((Q a)⁻¹ * Q.polarBilin (g x) a) • a := by
  change x - reflectionLinear Q a ha (g x) = (x-g x) + ((Q a)⁻¹ * Q.polarBilin (g x) a) • a
  rw [reflectionLinear_apply]
  abel

variable (u : residual Q g) (hu : Q u.val ≠ 0)

abbrev wallComplement : Submodule F (residual Q g) := (wallForm Q g u).ker

def wallProjection : residual Q g →ₗ[F] residual Q g :=
  LinearMap.id - ((Q u.val)⁻¹ • wallForm Q g u).smulRight u

@[simp] theorem wallProjection_apply (v : residual Q g) :
    wallProjection Q g u v = v - ((Q u.val)⁻¹ * wallForm Q g u v) • u := rfl

include hu in
theorem wallProjection_mem (v : residual Q g) : wallProjection Q g u v ∈ wallComplement Q g u := by
  change wallForm Q g u (wallProjection Q g u v) = 0
  rw [wallProjection_apply, map_sub, map_smul, smul_eq_mul, wallForm_self]
  field_simp
  ring

theorem wallProjection_fixed (v : wallComplement Q g u) : wallProjection Q g u v.val = v.val := by
  rw [wallProjection_apply]
  have hv : wallForm Q g u v.val = 0 := v.prop
  rw [hv, mul_zero, zero_smul, sub_zero]

/-- Composition with the reflection is exactly projection off its anisotropic residual vector. -/
theorem reflected_residual_projection (x : V) :
    residualMap Q (reflectedIsometry Q g u.val hu) x =
      (wallProjection Q g u ((residualMap Q g).rangeRestrict x)).val := by
  rw [reflected_residual, wallProjection_apply, wallForm_residual_right]
  change residualMap Q g x + ((Q u.val)⁻¹ * Q.polarBilin (g x) u.val) • u.val =
    residualMap Q g x - ((Q u.val)⁻¹ * -Q.polarBilin (g x) u.val) • u.val
  rw [mul_neg, neg_smul, sub_neg_eq_add]

/-- The new residual space is precisely the right Wall-perpendicular complement of u. -/
theorem reflected_residual_eq : residual Q (reflectedIsometry Q g u.val hu) =
    (wallComplement Q g u).map (residual Q g).subtype := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨wallProjection Q g u ((residualMap Q g).rangeRestrict x), wallProjection_mem Q g u hu _, ?_⟩
    exact (reflected_residual_projection Q g u hu x).symm
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, hx⟩ := (residualMap Q g).surjective_rangeRestrict v
    refine ⟨x, ?_⟩
    rw [reflected_residual_projection, hx]
    exact congrArg Subtype.val (wallProjection_fixed Q g u ⟨v, hv⟩)

/-- The residual of the reflected isometry embeds into the original residual. -/
def reflectedResidualInclusion : residual Q (reflectedIsometry Q g u.val hu) →ₗ[F]
    residual Q g :=
  (residual Q (reflectedIsometry Q g u.val hu)).inclusion (by
    rw [reflected_residual_eq]
    rintro y ⟨v, hv, rfl⟩
    exact v.prop)

theorem reflectedResidualInclusion_perp
    (v : residual Q (reflectedIsometry Q g u.val hu)) :
    wallForm Q g u (reflectedResidualInclusion Q g u hu v) = 0 := by
  have hv : v.val ∈ (wallComplement Q g u).map (residual Q g).subtype :=
    (congrArg (fun S : Submodule F V => v.val ∈ S)
      (reflected_residual_eq Q g u hu)).mp v.prop
  obtain ⟨w, hw, he⟩ := hv
  have hwv : w = reflectedResidualInclusion Q g u hu v := Subtype.ext he
  exact hwv ▸ hw

theorem reflectedResidualInclusion_map (x : V) :
    reflectedResidualInclusion Q g u hu
      ((residualMap Q (reflectedIsometry Q g u.val hu)).rangeRestrict x) =
    wallProjection Q g u ((residualMap Q g).rangeRestrict x) := by
  apply Subtype.ext
  exact reflected_residual_projection Q g u hu x

/-- The new Wall pairing is the restriction of the original Wall pairing. -/
theorem reflected_wallForm
    (v w : residual Q (reflectedIsometry Q g u.val hu)) :
    wallForm Q (reflectedIsometry Q g u.val hu) v w =
      wallForm Q g (reflectedResidualInclusion Q g u hu v)
        (reflectedResidualInclusion Q g u hu w) := by
  obtain ⟨x, rfl⟩ := (residualMap Q (reflectedIsometry Q g u.val hu)).surjective_rangeRestrict v
  rw [wallForm_residual, reflectedResidualInclusion_map, wallProjection_apply]
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    reflectedResidualInclusion_perp, smul_zero, sub_zero, wallForm_residual]
  rfl

/-- Actual linear equivalence onto the Wall-perpendicular space. -/
def reflectedResidualEquiv : residual Q (reflectedIsometry Q g u.val hu) ≃ₗ[F]
    wallComplement Q g u :=
  LinearEquiv.ofBijective
    ((reflectedResidualInclusion Q g u hu).codRestrict (wallComplement Q g u)
      (reflectedResidualInclusion_perp Q g u hu)) (by
    constructor
    · intro x y h
      exact Subtype.ext (congrArg (fun z : wallComplement Q g u => z.val.val) h)
    · intro v
      have hv : v.val.val ∈ residual Q (reflectedIsometry Q g u.val hu) := by
        rw [reflected_residual_eq]
        exact ⟨v.val, v.prop, rfl⟩
      exact ⟨⟨v.val.val, hv⟩, rfl⟩)

/-- Reflection in an anisotropic residual vector lowers residual dimension by one. -/
theorem reflected_residual_finrank [FiniteDimensional F V] :
    Module.finrank F (residual Q (reflectedIsometry Q g u.val hu)) + 1 =
      Module.finrank F (residual Q g) := by
  have hs : Function.Surjective (wallForm Q g u) := by
    intro c
    refine ⟨(c / Q u.val) • u, ?_⟩
    rw [map_smul, smul_eq_mul, wallForm_self]
    exact div_mul_cancel₀ c hu
  have h := (wallForm Q g u).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self] at h
  rw [(reflectedResidualEquiv Q g u hu).finrank_eq]
  exact (Nat.add_comm _ _).trans h

end ClassicalOrthogonal.IntrinsicWall


