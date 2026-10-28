/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianQuaternion.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.GoldenRational
public import Mathlib.Algebra.Quaternion

/-!
# IcosianQuaternion

Hamilton quaternions over the golden rational field carry a multiplicative
reduced norm and a rational trace pairing. A sum-of-squares identity proves
positivity and nondegeneracy of that pairing.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianQuaternion.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

/-- Hamilton quaternions over the golden field; quaternion conjugation fixes that field. -/
abbrev IcosianQuaternion := Quaternion GoldenRational

def icosianI : IcosianQuaternion := ⟨0,1,0,0⟩
def icosianJ : IcosianQuaternion := ⟨0,0,1,0⟩
def icosianK : IcosianQuaternion := ⟨0,0,0,1⟩

def icosianNorm (x : IcosianQuaternion) : GoldenRational := Quaternion.normSq x

def icosianFunctional (x : IcosianQuaternion) : ℚ := goldenFunctional x.re

theorem icosianI_sq : icosianI^2 = -1 := by
  ext <;> norm_num [icosianI,pow_two]

theorem icosianJ_sq : icosianJ^2 = -1 := by
  ext <;> norm_num [icosianJ,pow_two]

theorem icosianI_mul_J : icosianI*icosianJ=icosianK := by
  ext <;> norm_num [icosianI,icosianJ,icosianK]

theorem icosianJ_mul_I : icosianJ*icosianI= -icosianK := by
  ext <;> norm_num [icosianI,icosianJ,icosianK]

theorem icosianNorm_coordinates (x : IcosianQuaternion) :
    icosianNorm x=x.re^2+x.imI^2+x.imJ^2+x.imK^2 := Quaternion.normSq_def' x

theorem icosianNorm_mul (x y : IcosianQuaternion) :
    icosianNorm (x*y)=icosianNorm x*icosianNorm y := map_mul Quaternion.normSq x y

theorem icosianFunctional_star_mul_self (x : IcosianQuaternion) :
    icosianFunctional (star x*x)=
      goldenFunctional (x.re^2)+goldenFunctional (x.imI^2)+
        goldenFunctional (x.imJ^2)+goldenFunctional (x.imK^2) := by
  simp [icosianFunctional, goldenFunctional, Quaternion.re_mul, pow_two]

theorem icosianFunctional_star_mul_self_nonneg (x : IcosianQuaternion) :
    0 ≤ icosianFunctional (star x*x) := by
  rw [icosianFunctional_star_mul_self]
  exact add_nonneg (add_nonneg (add_nonneg (goldenFunctional_sq_nonneg _)
    (goldenFunctional_sq_nonneg _)) (goldenFunctional_sq_nonneg _))
      (goldenFunctional_sq_nonneg _)

theorem icosianFunctional_star_mul_self_eq_zero (x : IcosianQuaternion) :
    icosianFunctional (star x*x)=0 ↔ x=0 := by
  rw [icosianFunctional_star_mul_self]
  constructor
  · intro h
    have hr := goldenFunctional_sq_nonneg x.re
    have hi := goldenFunctional_sq_nonneg x.imI
    have hj := goldenFunctional_sq_nonneg x.imJ
    have hk := goldenFunctional_sq_nonneg x.imK
    have er := (goldenFunctional_sq_eq_zero x.re).mp (by linarith)
    have ei := (goldenFunctional_sq_eq_zero x.imI).mp (by linarith)
    have ej := (goldenFunctional_sq_eq_zero x.imJ).mp (by linarith)
    have ek := (goldenFunctional_sq_eq_zero x.imK).mp (by linarith)
    ext <;> simp [er,ei,ej,ek]
  · rintro rfl; simp [goldenFunctional]

/-- The precise rational pairing used to recover the quaternion-valued form is nondegenerate. -/
theorem icosianFunctional_pairing_nondegenerate (x : IcosianQuaternion)
    (h : ∀ a, icosianFunctional (a*x)=0) : x=0 :=
  (icosianFunctional_star_mul_self_eq_zero x).mp (h (star x))

theorem icosianFunctional_add (x y : IcosianQuaternion) :
    icosianFunctional (x+y)=icosianFunctional x+icosianFunctional y := rfl

theorem icosianFunctional_sub (x y : IcosianQuaternion) :
    icosianFunctional (x-y)=icosianFunctional x-icosianFunctional y := rfl

theorem icosianFunctional_mul_comm (x y : IcosianQuaternion) :
    icosianFunctional (x*y)=icosianFunctional (y*x) := by
  simp [icosianFunctional,Quaternion.re_mul,goldenFunctional]
  ring

theorem icosianFunctional_pairing_nondegenerate_right (x : IcosianQuaternion)
    (h : ∀ a, icosianFunctional (x*a)=0) : x=0 := by
  apply icosianFunctional_pairing_nondegenerate
  intro a
  rw [icosianFunctional_mul_comm]
  exact h a

/-- Equality of all weighted traces recovers the entire quaternion, not just its real part. -/
theorem icosianFunctional_pairing_ext (x y : IcosianQuaternion)
    (h : ∀ a, icosianFunctional (a*x)=icosianFunctional (a*y)) : x=y := by
  apply sub_eq_zero.mp
  apply icosianFunctional_pairing_nondegenerate
  intro a
  rw [mul_sub,icosianFunctional_sub,h,sub_self]

end Atlas.Algebra
