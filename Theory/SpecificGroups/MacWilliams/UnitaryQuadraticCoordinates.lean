module

public import Theory.SpecificGroups.MacWilliams.UnitaryFrame
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic

/-!
# Ten coefficients for binary quadratic maps

A quadratic map from the binary four-space to the binary two-space is determined
by four basis values and six polar values. The coefficient order is the four
diagonals, followed by the pairs `(1,0), (2,0), (2,1), (3,0), (3,1), (3,2)`.
Expanding in descending basis order uses only additivity in the first polar
argument. The given quadratic law also identifies the polar map uniquely.

The exposed coordinate functions are the finite input to the balanced
anisotropic normal-form problem for the MacWilliams unitary presentation.
The mathematical source is MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3, as cited in Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3(b), printed p.386.
-/

namespace MacWilliamsSylow

/-- Binary vector coordinates, with addition written multiplicatively. -/
public abbrev BinaryCoordinates (n : ℕ) := Multiplicative (Fin n → ZMod 2)

/-- Four diagonal and six off-diagonal values in the binary two-space. -/
public abbrev QuadraticCoefficients := Fin 10 → BinaryCoordinates 2

/-- Evaluate the quadratic polynomial in the specified coefficient order. -/
@[expose] public def coordinateSquare (c : QuadraticCoefficients)
    (x : BinaryCoordinates 4) : BinaryCoordinates 2 :=
  (if x.toAdd 0 = 1 then c 0 else 1) *
  (if x.toAdd 1 = 1 then c 1 else 1) *
  (if x.toAdd 2 = 1 then c 2 else 1) *
  (if x.toAdd 3 = 1 then c 3 else 1) *
  (if x.toAdd 1 = 1 ∧ x.toAdd 0 = 1 then c 4 else 1) *
  (if x.toAdd 2 = 1 ∧ x.toAdd 0 = 1 then c 5 else 1) *
  (if x.toAdd 2 = 1 ∧ x.toAdd 1 = 1 then c 6 else 1) *
  (if x.toAdd 3 = 1 ∧ x.toAdd 0 = 1 then c 7 else 1) *
  (if x.toAdd 3 = 1 ∧ x.toAdd 1 = 1 then c 8 else 1) *
  (if x.toAdd 3 = 1 ∧ x.toAdd 2 = 1 then c 9 else 1)

/-- The polar map of the coefficient polynomial, written multiplicatively. -/
@[expose] public def coordinatePolar (c : QuadraticCoefficients)
    (x y : BinaryCoordinates 4) : BinaryCoordinates 2 :=
  coordinateSquare c (x * y) * coordinateSquare c x * coordinateSquare c y

private def basisVector (i : Fin 4) : BinaryCoordinates 4 :=
  Multiplicative.ofAdd fun j => if j = i then 1 else 0

private def selectedVector (x : BinaryCoordinates 4) (i : Fin 4) : BinaryCoordinates 4 :=
  if x.toAdd i = 1 then basisVector i else 1

private theorem coordinates_decompose : ∀ x : BinaryCoordinates 4,
    x = selectedVector x 3 * selectedVector x 2 * selectedVector x 1 * selectedVector x 0 := by
  decide +kernel

/-- Every binary quadratic map in these dimensions has ten coefficients.
Only the stated quadratic law and first-argument polar additivity are needed. -/
public theorem exists_quadratic_coefficients
    (square : BinaryCoordinates 4 → BinaryCoordinates 2)
    (polar : BinaryCoordinates 4 → BinaryCoordinates 4 → BinaryCoordinates 2)
    (hone : square 1 = 1)
    (hquadratic : ∀ x y, square (x * y) = square x * square y * polar x y)
    (hbilinear : ∀ x y z, polar (x * y) z = polar x z * polar y z) :
    ∃ c : QuadraticCoefficients, square = coordinateSquare c ∧ polar = coordinatePolar c := by
  let c : QuadraticCoefficients := ![square (basisVector 0), square (basisVector 1),
    square (basisVector 2), square (basisVector 3),
    polar (basisVector 1) (basisVector 0), polar (basisVector 2) (basisVector 0),
    polar (basisVector 2) (basisVector 1), polar (basisVector 3) (basisVector 0),
    polar (basisVector 3) (basisVector 1), polar (basisVector 3) (basisVector 2)]
  have hsq : square = coordinateSquare c := by
    funext x
    calc
      square x = square (selectedVector x 3 * selectedVector x 2 *
          selectedVector x 1 * selectedVector x 0) := congrArg square (coordinates_decompose x)
      _ = coordinateSquare c x := by
        have binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        rcases binary (x.toAdd 0) with h0 | h0 <;>
          rcases binary (x.toAdd 1) with h1 | h1 <;>
          rcases binary (x.toAdd 2) with h2 | h2 <;>
          rcases binary (x.toAdd 3) with h3 | h3 <;>
          simp [selectedVector, coordinateSquare, h0, h1, h2, h3, c,
            hquadratic, hbilinear, hone] <;> ac_rfl
  refine ⟨c, hsq, ?_⟩
  funext x y
  have htwo : ∀ z : BinaryCoordinates 2, z * z = 1 := by decide +kernel
  have hpolar : polar x y = square (x * y) * square x * square y := by
    rw [hquadratic]
    calc
      polar x y = (square x * square x) * (square y * square y) * polar x y := by
        rw [htwo, htwo, one_mul, one_mul]
      _ = square x * square y * polar x y * square x * square y := by ac_rfl
  simpa only [hsq, coordinatePolar] using hpolar

end MacWilliamsSylow
