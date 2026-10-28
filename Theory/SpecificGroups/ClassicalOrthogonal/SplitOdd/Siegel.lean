/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-!
# Siegel transformations in arbitrary characteristic

Adapted from `Atlas/LinearAlgebra/QuadraticSiegel.lean` and the three polar
identities in `QuadraticHyperbolic.lean`. Imports and namespaces are narrowed
for CFSG / Lean 4.33. The formula preserves the quadratic form and has inverse
obtained by negating its perpendicular parameter, without division by two.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- The convention is the unhalved polar form, in every characteristic. -/
theorem add_smul (x y : V) (a : F) :
    Q (x + a • y) = Q x + a ^ 2 * Q y + a * Q.polarBilin x y := by
  rw [QuadraticMap.map_add Q, Q.map_smul]
  change Q x + (a * a) * Q y + Q.polarBilin x (a • y) = _
  rw [map_smul]
  simp only [smul_eq_mul, pow_two]

theorem polar_swap (x y : V) : Q.polarBilin x y = Q.polarBilin y x :=
  QuadraticMap.polar_comm Q x y

theorem polar_self (x : V) : Q.polarBilin x x = 2 * Q x := by
  change QuadraticMap.polar Q x x = _
  rw [QuadraticMap.polar_self]
  simp [two_smul, two_mul]

/-- The usual Siegel formula with unhalved polar pairing. -/
def siegel (u v x : V) : V :=
  x + Q.polarBilin x v • u - Q.polarBilin x u • v -
    (Q v * Q.polarBilin x u) • u

/-- The transformation fixes its singular direction. -/
theorem siegel_fix (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegel Q u v u = u := by
  have huu : Q.polarBilin u u = 0 := by rw [polar_self,hu,mul_zero]
  simp only [siegel,huv,huu,mul_zero,zero_smul,add_zero,sub_zero]

/-- Pairing with the singular direction is unchanged. -/
theorem siegel_pairing (u v x : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    Q.polarBilin (siegel Q u v x) u = Q.polarBilin x u := by
  have huu : Q.polarBilin u u = 0 := by rw [polar_self,hu,mul_zero]
  have hvu : Q.polarBilin v u = 0 := (polar_swap Q v u).trans huv
  simp only [siegel, map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, huu, hvu, mul_zero, add_zero, sub_zero]

/-- Preservation of the actual quadratic form, not merely of its polar form. -/
theorem siegel_preserves (u v x : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) : Q (siegel Q u v x) = Q x := by
  have huu : Q.polarBilin u u = 0 := by rw [polar_self,hu,mul_zero]
  have hvu : Q.polarBilin v u = 0 := (polar_swap Q v u).trans huv
  simp only [siegel, sub_eq_add_neg, ← neg_smul, add_smul,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hu, huv, huu, hvu]
  ring

@[simp] theorem siegel_zero (u x : V) : siegel Q u 0 x = x := by
  simp [siegel]

/-- Addition of perpendicular parameters is composition of transformations. -/
theorem siegel_add (u v w x : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) (huw : Q.polarBilin u w = 0) :
    siegel Q u v (siegel Q u w x) = siegel Q u (v+w) x := by
  have huu : Q.polarBilin u u = 0 := by rw [polar_self,hu,mul_zero]
  have hwu : Q.polarBilin w u = 0 := (polar_swap Q w u).trans huw
  have hwv : Q.polarBilin w v = Q.polarBilin v w := polar_swap Q w v
  have hq : Q (v+w) = Q v + Q w + Q.polarBilin v w := QuadraticMap.map_add Q v w
  simp only [siegel, map_sub, map_add, map_smul, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, huu, huv, hwu,
    mul_zero, add_zero, sub_zero, hwv, hq]
  module

/-- The negative parameter is the inverse, uniformly in characteristic two as well. -/
theorem siegel_inverse (u v x : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegel Q u (-v) (siegel Q u v x) = x := by
  have huv' : Q.polarBilin u (-v) = 0 := by rw [map_neg,huv,neg_zero]
  rw [siegel_add Q u (-v) v x hu huv' huv, neg_add_cancel, siegel_zero]

/-- The formula is linear independently of its isometry hypotheses. -/
def siegelLinear (u v : V) : V →ₗ[F] V where
  toFun := siegel Q u v
  map_add' x y := by
    simp only [siegel,map_add,LinearMap.add_apply]
    module
  map_smul' a x := by
    simp only [siegel,map_smul,LinearMap.smul_apply,smul_eq_mul,RingHom.id_apply]
    module

/-- The actual quadratic isometry with inverse parameter -v. -/
def siegelIsometry (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    Q.IsometryEquiv Q where
  toFun := siegel Q u v
  invFun := siegel Q u (-v)
  left_inv x := siegel_inverse Q u v x hu huv
  right_inv x := by
    have hn : Q.polarBilin u (-v) = 0 := by rw [map_neg,huv,neg_zero]
    simpa only [neg_neg] using siegel_inverse Q u (-v) x hu hn
  map_add' := (siegelLinear Q u v).map_add
  map_smul' := (siegelLinear Q u v).map_smul
  map_app' x := siegel_preserves Q u v x hu huv

/-- Changing the singular-line representative rescales the parameter. -/
theorem siegel_scale (u v x : V) (a : F) :
    siegel Q (a • u) v x = siegel Q u (a • v) x := by
  simp only [siegel,Q.map_smul,map_smul,smul_eq_mul]
  module

/-- Adding a multiple of the singular vector does not change its transformation. -/
theorem siegel_parameter_mod_line (u v x : V) (a : F) (hu : Q u=0)
    (huv : Q.polarBilin u v=0) : siegel Q u (v+a • u) x = siegel Q u v x := by
  have hvu : Q.polarBilin v u=0 := (polar_swap Q v u).trans huv
  have hq : Q (v+a • u)=Q v := by rw [add_smul,hu,hvu]; ring
  simp only [siegel,hq,map_add,map_smul,smul_eq_mul]
  module

theorem isometry_polar (g : Q.IsometryEquiv Q) (x y : V) :
    Q.polarBilin (g x) (g y)=Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,← map_add,g.map_app]

/-- Conjugation covariance on the actual quadratic space. -/
theorem siegel_covariant (g : Q.IsometryEquiv Q) (u v x : V) :
    g (siegel Q u v x) = siegel Q (g u) (g v) (g x) := by
  simp only [siegel,map_sub,map_add,map_smul,isometry_polar,g.map_app]

end ClassicalOrthogonal.Quadratic



