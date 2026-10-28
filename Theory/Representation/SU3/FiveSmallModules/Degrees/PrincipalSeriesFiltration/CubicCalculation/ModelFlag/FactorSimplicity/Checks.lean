module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Data
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate.Checked
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate.Agreement

/-!
# Checked image and middle-quotient coordinates

The complement columns W, projection rows S and inverse rows P give
I = UP + WS + RV, SW = I, SU = VW = 0. Hence S induces coordinates on
ker N / range N. The two generator comparisons are checked in the same
column convention as the original model. All finite computations below are
Lean kernel reductions of packed bit operations, interpreted by PackedRows.
Source motivation: Guralnick–Malle Proposition 4.3, p.10;
Aschbacher–Smith K.2, p.453.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
open Certificate Certificate.Packed

private theorem matrix_add_rows {m n : ℕ} (a b : Fin m → Row) :
    matrix n (fun i => add (a i) (b i)) = matrix n a + matrix n b := by
  apply Matrix.ext
  intro i j
  exact entry_add _ _ _

theorem image_intertwining (a : Fin 2) :
    matrix 126 (G a) * matrix 21 U = matrix 21 U * imageMatrices a := by
  have he : ∀ a i, mul (G a) U i = mul U (A a) i := by decide +kernel
  rw [imageMatrices, ← matrix_mul, ← matrix_mul, funext (he a)]

theorem middle_left_inverse : matrix 126 S * matrix 84 W = 1 := by
  have he : ∀ i, mul S W i = identity 84 i := by decide +kernel
  rw [← matrix_mul, funext he, matrix_identity]

theorem middle_annihilates_image : matrix 126 S * matrix 21 U = 0 := by
  have he : ∀ i, mul S U i = (0, 0) := by decide +kernel
  rw [← matrix_mul, funext he, matrix_zero]

theorem middle_in_kernel : matrix 126 V * matrix 84 W = 0 := by
  have he : ∀ i, mul V W i = (0, 0) := by decide +kernel
  rw [← matrix_mul, funext he, matrix_zero]

theorem decomposition :
    matrix 21 U * matrix 126 P + matrix 84 W * matrix 126 S +
      matrix 21 R * matrix 126 V = 1 := by
  have he : ∀ i, add (add (mul U P i) (mul W S i)) (mul R V i) =
      identity 126 i := by decide +kernel
  rw [← matrix_mul, ← matrix_mul, ← matrix_mul, ← matrix_add_rows,
    ← matrix_add_rows, funext he, matrix_identity]

theorem middle_intertwining (a : Fin 2) :
    matrix 126 S * matrix 126 (G a) =
      middleMatrices a * matrix 126 S + matrix 21 (H a) * matrix 126 V := by
  have he : ∀ a i, mul S (G a) i = add (mul (B a) S i) (mul (H a) V i) :=
    by decide +kernel
  rw [middleMatrices, ← matrix_mul, ← matrix_mul, ← matrix_mul,
    ← matrix_add_rows, funext (he a)]

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
