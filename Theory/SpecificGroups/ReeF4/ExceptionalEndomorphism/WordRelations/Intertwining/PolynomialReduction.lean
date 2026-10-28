module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Coordinates

/-!
# Divided-power reduction for the exceptional comparison

The F4 root curves are cubic divided-power polynomials. For a geometrically
long root, intertwining follows coefficient by coefficient. For a short root,
the target parameter is squared: odd source coefficients and target terms of
degrees four and six must vanish. This elementary reduction isolates those
eight concrete matrix identities from the polynomial algebra.
-/

public section

namespace ReeF4.WordRelations

open scoped Matrix

variable {K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]

/-- The coefficient comparison for an unchanged root parameter. -/
theorem intertwines_cubic_of_linear_coefficients
    (T A₁ A₂ A₃ B₁ B₂ B₃ : Matrix n n K) (t : K)
    (h₁ : T * A₁ = B₁ * T) (h₂ : T * A₂ = B₂ * T)
    (h₃ : T * A₃ = B₃ * T) :
    T * (1 + t • A₁ + t ^ 2 • A₂ + t ^ 3 • A₃) =
      (1 + t • B₁ + t ^ 2 • B₂ + t ^ 3 • B₃) * T := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, h₁, h₂, h₃]

/-- The coefficient comparison when the target root parameter is squared. -/
theorem intertwines_cubic_of_squared_coefficients
    (T A₁ A₂ A₃ B₁ B₂ B₃ : Matrix n n K) (t : K)
    (h₁ : T * A₁ = 0) (h₂ : T * A₂ = B₁ * T)
    (h₃ : T * A₃ = 0) (h₄ : B₂ * T = 0) (h₆ : B₃ * T = 0) :
    T * (1 + t • A₁ + t ^ 2 • A₂ + t ^ 3 • A₃) =
      (1 + (t ^ 2) • B₁ + (t ^ 2) ^ 2 • B₂ +
        (t ^ 2) ^ 3 • B₃) * T := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, h₁, h₂, h₃, h₄, h₆]
  simp

end ReeF4.WordRelations
