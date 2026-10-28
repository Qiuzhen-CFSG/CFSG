module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate.Values

/-!
# Kernel-checked identities for the cubic matrices

All computation here is kernel reduction of natural-number bit operations.
The general PackedRows proofs interpret the results in the original coefficient
algebra. In particular, agreement with Data.lean is checked explicitly, so the
certificate is about its fixed matrices, not a replacement representation.
The short factorization N = UV, LU = VR = I, VU = 0 supplies rank and square-zero;
the two commutation checks are independent. Source: Guralnick–Malle,
Proposition 4.3, p.10 (cubic principal-series calculation).
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.Certificate
open Packed

theorem factorization : matrix 126 N = matrix 21 U * matrix 126 V := by
  have h : ∀ i, mul U V i = N i := by decide +kernel
  rw [← matrix_mul, funext h]

theorem left_inverse : matrix 126 L * matrix 21 U = 1 := by
  have h : ∀ i, mul L U i = identity 21 i := by decide +kernel
  rw [← matrix_mul, funext h, matrix_identity]

theorem right_inverse : matrix 126 V * matrix 21 R = 1 := by
  have h : ∀ i, mul V R i = identity 21 i := by decide +kernel
  rw [← matrix_mul, funext h, matrix_identity]

theorem annihilation : matrix 126 V * matrix 21 U = 0 := by
  have h : ∀ i, mul V U i = (0,0) := by decide +kernel
  rw [← matrix_mul, funext h, matrix_zero]

theorem commutation (a : Fin 2) :
    matrix 126 N * matrix 126 (G a) = matrix 126 (G a) * matrix 126 N := by
  have h : ∀ a i, mul N (G a) i = mul (G a) N i := by decide +kernel
  rw [← matrix_mul, ← matrix_mul, funext (h a)]


end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.Certificate
