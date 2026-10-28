module
public import Theory.SpecificGroups.GL2.DiagonalSwap

/-!
# Squares and determinants of actual twisted coordinate swaps

Over any field, the coordinate-swap matrix has determinant -1. Multiplying
it by diag(ζ,1), for a unit ζ, gives a matrix with determinant -ζ and square
ζI. Direct entrywise multiplication and the two-by-two determinant formula
prove these identities; no finiteness or characteristic condition is needed.

These are shared matrix calculations for the actual exterior elements in
the linear and unitary determinant models. Source: Alperin--Brauer--Gorenstein
II.2 Lemma 1, article p17, and II.3 Proposition 3, article p26. The equations
concern the common underlying GL2 matrices, so their consumers can retain
the original determinant and Hermitian subgroup membership proofs.
-/

namespace Matrix.GeneralLinearGroup
public theorem coordinateSwap_det (F : Type*) [Field F] :
    det (coordinateSwap F) = (-1 : Fˣ) := by
  apply Units.ext
  change (coordinateSwap F).val.det = (-1 : F)
  simp [coordinateSwap_val, Matrix.det_fin_two]

public theorem diagonalPair_coordinateSwap_sq (F : Type*) [Field F] (ζ : Fˣ) :
    (diagonalPair F (ζ, 1) * coordinateSwap F) ^ 2 = scalar (Fin 2) ζ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, diagonalPair, coordinateSwap, Matrix.mul_apply, Fin.sum_univ_two,
      coe_scalar, Matrix.scalar_apply]

public theorem diagonalPair_coordinateSwap_det (F : Type*) [Field F] (ζ : Fˣ) :
    det (diagonalPair F (ζ, 1) * coordinateSwap F) = -ζ := by
  rw [map_mul, coordinateSwap_det]
  have hdg : det (diagonalPair F (ζ, 1)) = ζ := by
    apply Units.ext
    change (diagonalPair F (ζ, 1)).val.det = (ζ : F)
    simp [diagonalPair_val, Matrix.det_fin_two]
  rw [hdg]
  simp
end Matrix.GeneralLinearGroup
