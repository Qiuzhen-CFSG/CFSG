module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Frame.Data
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Data

/-!
# Checked inverse for the Rudvalis frame matrix

A single GF(5) matrix-product certificate proves the left inverse equation.
Finiteness then gives the right inverse equation, without another finite
product calculation or expansion of a determinant. All numerical computation
is checked by Lean's kernel through `checkProduct_sound`.

Source: the untrusted inverse in `DoubleCover/source/frame.json`.
-/

namespace Rudvalis.Multiplier.DoubleCover.Frame
public section

/-- The supplied inverse is a left inverse, certified over GF(5). -/
theorem inverse_mul_basis : inverseMatrix * basisMatrix = 1 := by
  calc
    inverseMatrix * basisMatrix = matrixOne :=
      checkProduct_sound _ _ _ (by decide +kernel)
    _ = 1 := by decide +kernel

/-- A left inverse of this finite square matrix is also a right inverse. -/
theorem basis_mul_inverse : basisMatrix * inverseMatrix = 1 :=
  (mul_eq_one_comm (a := inverseMatrix) (b := basisMatrix)).mp inverse_mul_basis

end
end Rudvalis.Multiplier.DoubleCover.Frame
