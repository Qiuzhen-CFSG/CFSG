/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/Scalars.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.EisensteinRational
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Exact Fischer scalars

The rational Eisenstein field supplies the three scalar phases and its
complex embedding. Explicit quadratic-coordinate calculations establish
the conjugation, phase, and embedding identities.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/Scalars.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream coordinate calculations.
-/

@[expose] public section

namespace Atlas.Fischer
open Atlas.Algebra
open scoped QuadraticAlgebra

/-- The retained Eisenstein rational field, with its existing conjugation. -/
abbrev Scalar := EisensteinRational
abbrev omega : Scalar := rationalOmega

def theta : Scalar := omega - star omega

theorem omega_conjugate : star omega = omega ^ 2 := by
  ext <;> norm_num [rationalOmega, QuadraticAlgebra.omega, pow_two]

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  norm_num [rationalOmega, QuadraticAlgebra.omega] at this

theorem theta_sq : theta ^ 2 = -3 := by
  ext <;> norm_num [theta, rationalOmega, QuadraticAlgebra.omega, pow_two]

theorem theta_conjugate : star theta = -theta := by simp [theta, sub_eq_add_neg]

theorem theta_integral : theta = eisensteinToRational eisensteinTheta := by
  ext <;> norm_num [theta, rationalOmega, eisensteinTheta, eisensteinOmega,
    eisensteinToRational, QuadraticAlgebra.omega]

theorem cube_eq_one_iff (z : Scalar) : z ^ 3 = 1 ↔
    z = 1 ∨ z = omega ∨ z = omega ^ 2 := by
  have hf : (z - 1) * (z - omega) * (z - omega ^ 2) = z ^ 3 - 1 := by
    have h := rationalOmega_relation
    have hc := rationalOmega_cube
    calc
      _ = z ^ 3 - 1 + (omega ^ 2 + omega + 1) * (z - z ^ 2) + (omega ^ 3 - 1) * (z - 1) := by ring
      _ = _ := by rw [h, hc]; ring
  constructor
  · intro h
    have : (z - 1) * (z - omega) * (z - omega ^ 2) = 0 := by rw [hf, h]; ring
    simpa only [mul_eq_zero, sub_eq_zero, or_assoc] using this
  · rintro (rfl | rfl | rfl)
    · simp
    · exact rationalOmega_cube
    · rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, rationalOmega_cube]; simp

/-- The actual three cube roots, as a subgroup of the scalar units. -/
abbrev Mu3 := rootsOfUnity 3 Scalar

def cubeRootValues : Finset Scalar := {1, omega, omega ^ 2}

theorem mem_cubeRootValues (z : Scalar) : z ∈ cubeRootValues ↔ z ^ 3 = 1 := by
  simp only [cubeRootValues, Finset.mem_insert, Finset.mem_singleton]
  exact (cube_eq_one_iff z).symm

noncomputable def mu3EquivValues : Mu3 ≃ cubeRootValues where
  toFun u := ⟨u.val.val, (mem_cubeRootValues _).mpr ((mem_rootsOfUnity' _ _).mp u.prop)⟩
  invFun z := ⟨Units.mk0 z.val (by
    intro h
    have hc := (mem_cubeRootValues _).mp z.prop
    rw [h] at hc
    norm_num at hc), (mem_rootsOfUnity' _ _).mpr ((mem_cubeRootValues _).mp z.prop)⟩
  left_inv u := by apply Subtype.ext; apply Units.ext; rfl
  right_inv z := by rfl

theorem cubeRootValues_card : cubeRootValues.card = 3 := by decide +kernel

theorem mu3_card : Nat.card Mu3 = 3 := by
  rw [Nat.card_congr mu3EquivValues, Nat.card_eq_fintype_card, Fintype.card_coe,
    cubeRootValues_card]

noncomputable def complexOmega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private theorem complexOmega_relation : complexOmega * complexOmega =
    (-1 : ℚ) • (1 : ℂ) + (-1 : ℚ) • complexOmega := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [complexOmega, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The embedding chooses the root with positive imaginary part. -/
noncomputable def scalarToComplex : Scalar →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨complexOmega, by exact complexOmega_relation⟩

theorem scalarToComplex_injective : Function.Injective scalarToComplex :=
  scalarToComplex.injective

theorem scalarToComplex_apply (z : Scalar) :
    scalarToComplex z = (z.re : ℂ) + (z.im : ℂ) * complexOmega := by
  change z.re • (1 : ℂ) + z.im • complexOmega = _
  simp [Algebra.smul_def]

theorem scalarToComplex_omega : scalarToComplex omega = complexOmega := by
  simp [scalarToComplex_apply, rationalOmega, QuadraticAlgebra.omega]

theorem scalarToComplex_star (z : Scalar) :
    scalarToComplex (star z) = star (scalarToComplex z) := by
  apply Complex.ext <;> simp [scalarToComplex_apply, complexOmega]; ring

theorem scalarToComplex_real (z : Scalar) :
    (scalarToComplex z).re = (eisensteinReal z : ℝ) := by
  simp [scalarToComplex_apply, complexOmega, eisensteinReal]
  ring

end Atlas.Fischer
