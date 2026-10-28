module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FinCases

/-!
# Two small matrix facts for the order-twelve five-plane actor

In GL₂(5), an involution of determinant one is scalar. An element of
determinant minus one whose sixth power is one is an involution.

The proofs check the 625 possible matrices in four coordinates, using
kernel reduction. The coordinate multiplication is proved to be the literal
matrix multiplication. These two facts supply the central involution and
inverting reflection in the recognition argument for Aschbacher,
*Sporadic Groups* (1994), 47.2, printed p.261.
-/

namespace Matrix.FivePlaneTwelveActor

private abbrev Coordinates := (ZMod 5 × ZMod 5) × (ZMod 5 × ZMod 5)
private abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 5)

private def multiply (a b : Coordinates) : Coordinates :=
  ((a.1.1 * b.1.1 + a.1.2 * b.2.1, a.1.1 * b.1.2 + a.1.2 * b.2.2),
   (a.2.1 * b.1.1 + a.2.2 * b.2.1, a.2.1 * b.1.2 + a.2.2 * b.2.2))

private def determinant (a : Coordinates) : ZMod 5 :=
  a.1.1 * a.2.2 - a.1.2 * a.2.1

private def identity : Coordinates := ((1, 0), (0, 1))
private def negativeIdentity : Coordinates := ((-1, 0), (0, -1))

private theorem involution_certificate : ∀ a : Coordinates,
    determinant a = 1 → multiply a a = identity →
      a = identity ∨ a = negativeIdentity := by
  decide +kernel

private theorem sixth_power_certificate : ∀ a : Coordinates,
    determinant a = -1 →
    (let a3 := multiply (multiply a a) a; multiply a3 a3 = identity) →
      multiply a a = identity := by
  decide +kernel

private def coordinates (A : Mat) : Coordinates :=
  ((A 0 0, A 0 1), (A 1 0, A 1 1))

private theorem coordinates_injective : Function.Injective coordinates := by
  intro A B h
  simp only [coordinates, Prod.mk.injEq] at h
  ext i j
  fin_cases i <;> fin_cases j
  · exact h.1.1
  · exact h.1.2
  · exact h.2.1
  · exact h.2.2

private theorem coordinates_mul (A B : Mat) :
    coordinates (A * B) = multiply (coordinates A) (coordinates B) := by
  simp [coordinates, multiply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem coordinates_det (A : Mat) :
    determinant (coordinates A) = A.det := by
  simp [coordinates, determinant, Matrix.det_fin_two]

/-- A determinant-one involution on the five-plane is scalar. -/
public theorem eq_one_or_neg_one_of_det_one_of_sq_one
    (A : GeneralLinearGroup (Fin 2) (ZMod 5))
    (hd : GeneralLinearGroup.det A = 1) (hA : A ^ 2 = 1) :
    A = 1 ∨ A = -1 := by
  have hd' : determinant (coordinates A.val) = 1 := by
    rw [coordinates_det]
    exact congrArg Units.val hd
  have hA' : multiply (coordinates A.val) (coordinates A.val) = identity := by
    rw [← coordinates_mul]
    have h : A.val * A.val = 1 := by
      simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val hA
    rw [h]
    rfl
  rcases involution_certificate (coordinates A.val) hd' hA' with h | h
  · exact Or.inl (Units.ext (coordinates_injective h))
  · exact Or.inr (Units.ext (coordinates_injective h))

/-- A determinant-minus-one matrix of exponent dividing six is an involution. -/
public theorem sq_eq_one_of_det_neg_one_of_pow_six
    (A : GeneralLinearGroup (Fin 2) (ZMod 5))
    (hd : GeneralLinearGroup.det A = -1) (hA : A ^ 6 = 1) :
    A ^ 2 = 1 := by
  have hd' : determinant (coordinates A.val) = -1 := by
    rw [coordinates_det]
    exact congrArg Units.val hd
  have hA' : (let a := coordinates A.val;
      let a3 := multiply (multiply a a) a; multiply a3 a3 = identity) := by
    dsimp only
    rw [← coordinates_mul, ← coordinates_mul, ← coordinates_mul]
    have h : (A.val * A.val * A.val) * (A.val * A.val * A.val) = 1 := by
      have h' : (A.val ^ 3) ^ 2 = 1 := by
        simpa only [← pow_mul, Units.val_pow_eq_pow_val, Units.val_one] using
          congrArg Units.val hA
      simpa only [pow_succ, pow_zero, one_mul] using h'
    rw [h]
    rfl
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
  apply coordinates_injective
  rw [coordinates_mul]
  exact sixth_power_certificate (coordinates A.val) hd' hA'

end Matrix.FivePlaneTwelveActor
