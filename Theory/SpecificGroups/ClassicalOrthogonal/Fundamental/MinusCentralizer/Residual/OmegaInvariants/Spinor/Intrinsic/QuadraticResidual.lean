/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/QuadraticResidual.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and a separate IntrinsicWall namespace for the residual 1-g normalization.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Siegel
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Residual spaces and their canonical Wall pairing

The residual is the image of `1-g`. Pairing a lift of the first argument
with the second via the unhalved polar form gives a section-independent form.
Fixed-vector orthogonality proves nondegeneracy, and its diagonal is `Q(u)`.
This is the normalization used by the intrinsic spinor character.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace ClassicalOrthogonal.IntrinsicWall
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (g : Q.IsometryEquiv Q)

def residualMap : V →ₗ[F] V := LinearMap.id - g.toLinearEquiv.toLinearMap

abbrev residual : Submodule F V := (residualMap Q g).range

@[simp] theorem residualMap_apply (x : V) : residualMap Q g x = x - g x := rfl

def residualSection : residual Q g →ₗ[F] V :=
  Classical.choose ((residualMap Q g).rangeRestrict.exists_rightInverse_of_surjective
    (residualMap Q g).range_rangeRestrict)

theorem residualSection_spec (u : residual Q g) : residualMap Q g (residualSection Q g u) = u.val := by
  have h := Classical.choose_spec ((residualMap Q g).rangeRestrict.exists_rightInverse_of_surjective
    (residualMap Q g).range_rangeRestrict)
  exact congrArg Subtype.val (LinearMap.congr_fun h u)

/-- Fixed vectors are perpendicular to the residual space. -/
theorem fixed_perpendicular_residual (x : V) (hx : g x = x) (u : residual Q g) :
    Q.polarBilin x u.val = 0 := by
  obtain ⟨y, hy⟩ := u.prop
  change residualMap Q g y = u.val at hy
  rw [← hy, residualMap_apply, map_sub]
  have h := isometry_polar Q g x y
  rw [hx] at h
  exact sub_eq_zero.mpr h.symm

/-- The Wall form uses any linear section; its value is independent of that choice. -/
def wallForm : LinearMap.BilinForm F (residual Q g) :=
  LinearMap.BilinForm.comp Q.polarBilin (residualSection Q g) (residual Q g).subtype

/-- The defining, section-independent equation for Wall's residual form. -/
theorem wallForm_residual (x : V) (v : residual Q g) :
    wallForm Q g ((residualMap Q g).rangeRestrict x) v = Q.polarBilin x v.val := by
  let u := (residualMap Q g).rangeRestrict x
  have hsec := residualSection_spec Q g u
  have hf : g (residualSection Q g u - x) = residualSection Q g u - x := by
    have he : residualSection Q g u - g (residualSection Q g u) = x - g x := hsec
    rw [map_sub]
    have ht := congrArg (fun t : V => residualSection Q g u - t - g x) he
    convert ht using 1 <;> abel
  have hp := fixed_perpendicular_residual Q g (residualSection Q g u - x) hf v
  rw [map_sub, LinearMap.sub_apply] at hp
  exact sub_eq_zero.mp hp

/-- The Wall form's diagonal is the original quadratic value. -/
theorem wallForm_self (u : residual Q g) : wallForm Q g u u = Q u.val := by
  obtain ⟨x, hx⟩ := (residualMap Q g).surjective_rangeRestrict u
  rw [← hx, wallForm_residual]
  change Q.polarBilin x (x-g x) = Q (x-g x)
  conv_rhs => rw [sub_eq_add_neg, ← neg_one_smul F (g x), ClassicalOrthogonal.Quadratic.add_smul, g.map_app]
  rw [map_sub, polar_self]
  ring

/-- Symmetrization of Wall's form is the restricted polar form, in every characteristic. -/
theorem wallForm_symmetrization (u v : residual Q g) :
    wallForm Q g u v + wallForm Q g v u = Q.polarBilin u.val v.val := by
  obtain ⟨x, hx⟩ := (residualMap Q g).surjective_rangeRestrict u
  obtain ⟨y, hy⟩ := (residualMap Q g).surjective_rangeRestrict v
  rw [← hx, ← hy, wallForm_residual, wallForm_residual]
  change Q.polarBilin x (y-g y) + Q.polarBilin y (x-g x) = Q.polarBilin (x-g x) (y-g y)
  simp only [map_sub, LinearMap.sub_apply]
  rw [isometry_polar, polar_swap Q y x, polar_swap Q y (g x)]
  ring


/-- The intrinsic residual equation uniquely determines the Wall pairing. -/
theorem wallForm_unique (B : LinearMap.BilinForm F (residual Q g))
    (hB : ∀ x v, B ((residualMap Q g).rangeRestrict x) v = Q.polarBilin x v.val) :
    B = wallForm Q g := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  obtain ⟨x, hx⟩ := (residualMap Q g).surjective_rangeRestrict u
  rw [← hx, hB, wallForm_residual]

theorem fixed_iff_perpendicular_residual (hQ : Q.polarBilin.Nondegenerate) (x : V) :
    g x = x ↔ ∀ u : residual Q g, Q.polarBilin x u.val = 0 := by
  constructor
  · exact fixed_perpendicular_residual Q g x
  · intro h
    apply sub_eq_zero.mp
    apply hQ.1
    intro y
    have hp := h ((residualMap Q g).rangeRestrict (g.symm y))
    change Q.polarBilin x (g.symm y - g (g.symm y)) = 0 at hp
    rw [g.apply_symm_apply, map_sub] at hp
    have ht := isometry_polar Q g x (g.symm y)
    rw [g.apply_symm_apply] at ht
    rw [map_sub, LinearMap.sub_apply, ht]
    exact hp

/-- The residual Wall form is nondegenerate whenever the original polar form is nondegenerate. -/
theorem wallForm_nondegenerate (hQ : Q.polarBilin.Nondegenerate) :
    (wallForm Q g).Nondegenerate := by
  constructor
  · intro u hu
    let x := residualSection Q g u
    have hx : g x = x := (fixed_iff_perpendicular_residual Q g hQ x).mpr hu
    apply Subtype.ext
    have hr := residualSection_spec Q g u
    change x - g x = u.val at hr
    rw [hx, sub_self] at hr
    exact hr.symm
  · intro v hv
    apply Subtype.ext
    apply hQ.2
    intro x
    exact (wallForm_residual Q g x v).symm.trans (hv ((residualMap Q g).rangeRestrict x))

end ClassicalOrthogonal.IntrinsicWall
