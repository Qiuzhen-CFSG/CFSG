module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.MatrixRelations
import Mathlib.Tactic.FinCases

/-!
# Certified relations of the eleven local kernel words

These witnesses implement the ATLAS `J4G1-max1W1` words documented in
`Cardinality.Subgroup` and the conjugates in `KernelCount.BinarySpan`.
Packed products are checked by Lean's kernel; `decode_packedMul` transfers
these certificates to binary matrices. No external computation is trusted.
-/

public section
namespace Janko4.Cardinality.KernelCount
open Relations
open Janko4.GeneratorCertificates

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- All eleven candidate rows evaluate the actual conjugate words. -/
theorem representation_basis (i : Fin 11) :
    representation hA hB (basis hA hB i) = decodeRows (basisRows i) := by
  have h0 : representation hA hB (basis hA hB 0) = decodeRows e0Rows :=
    representation_seed hA hB
  have h1 : representation hA hB (basis hA hB 1) = decodeRows e1Rows :=
    eval_conj (representation hA hB) h0 (representation_x hA hB) matrix_x0
  have h2 : representation hA hB (basis hA hB 2) = decodeRows e2Rows :=
    eval_conj (representation hA hB) h0 (representation_y hA hB) matrix_y0
  have h3 : representation hA hB (basis hA hB 3) = decodeRows e3Rows :=
    eval_conj (representation hA hB) h2 (representation_x hA hB) matrix_x2
  have h4 : representation hA hB (basis hA hB 4) = decodeRows e4Rows :=
    eval_conj (representation hA hB) h3 (representation_y hA hB) matrix_y3
  have h5 : representation hA hB (basis hA hB 5) = decodeRows e5Rows :=
    eval_conj (representation hA hB) h4 (representation_y hA hB) matrix_y4
  have h6 : representation hA hB (basis hA hB 6) = decodeRows e6Rows :=
    eval_conj (representation hA hB) h5 (representation_x hA hB) matrix_x5
  have h7 : representation hA hB (basis hA hB 7) = decodeRows e7Rows :=
    eval_conj (representation hA hB) h6 (representation_y hA hB) matrix_y6
  have h8 : representation hA hB (basis hA hB 8) = decodeRows e8Rows :=
    eval_conj (representation hA hB) h7 (representation_y hA hB) matrix_y7
  have h9 : representation hA hB (basis hA hB 9) = decodeRows e9Rows :=
    eval_conj (representation hA hB) h8 (representation_x hA hB) matrix_x8
  have h10 : representation hA hB (basis hA hB 10) = decodeRows e10Rows :=
    eval_conj (representation hA hB) h9 (representation_y hA hB) matrix_y9
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

/-- Each conjugate is an involution in the sense needed by binary span. -/
theorem basis_square (i : Fin 11) : basis hA hB i * basis hA hB i = 1 := by
  have h0 : localKernelSeed hA hB * localKernelSeed hA hB = 1 := by
    apply representation_injective hA hB
    rw [map_mul, map_one, representation_seed,
      decoded_product product_square0, decode_packedOne]
  have step (g a : max1Subgroup hA hB) (ha : a * a = 1) :
      (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc
      _ = g⁻¹ * (a * a) * g := by simp only [mul_assoc, mul_inv_cancel_left]
      _ = 1 := by rw [ha, mul_one, inv_mul_cancel]
  have hs0 : basis hA hB 0 * basis hA hB 0 = 1 := h0
  have hs1 : basis hA hB 1 * basis hA hB 1 = 1 :=
    step (localX hA hB) (basis hA hB 0) hs0
  have hs2 : basis hA hB 2 * basis hA hB 2 = 1 :=
    step (localY hA hB) (basis hA hB 0) hs0
  have hs3 : basis hA hB 3 * basis hA hB 3 = 1 :=
    step (localX hA hB) (basis hA hB 2) hs2
  have hs4 : basis hA hB 4 * basis hA hB 4 = 1 :=
    step (localY hA hB) (basis hA hB 3) hs3
  have hs5 : basis hA hB 5 * basis hA hB 5 = 1 :=
    step (localY hA hB) (basis hA hB 4) hs4
  have hs6 : basis hA hB 6 * basis hA hB 6 = 1 :=
    step (localX hA hB) (basis hA hB 5) hs5
  have hs7 : basis hA hB 7 * basis hA hB 7 = 1 :=
    step (localY hA hB) (basis hA hB 6) hs6
  have hs8 : basis hA hB 8 * basis hA hB 8 = 1 :=
    step (localY hA hB) (basis hA hB 7) hs7
  have hs9 : basis hA hB 9 * basis hA hB 9 = 1 :=
    step (localX hA hB) (basis hA hB 8) hs8
  have hs10 : basis hA hB 10 * basis hA hB 10 = 1 :=
    step (localY hA hB) (basis hA hB 9) hs9
  fin_cases i
  · exact hs0
  · exact hs1
  · exact hs2
  · exact hs3
  · exact hs4
  · exact hs5
  · exact hs6
  · exact hs7
  · exact hs8
  · exact hs9
  · exact hs10

/-- The eleven actual kernel words commute pairwise. -/
theorem basis_commute (i j : Fin 11) : Commute (basis hA hB i) (basis hA hB j) := by
  apply representation_injective hA hB
  simpa only [map_mul, representation_basis] using (matrix_commute i j).eq

/-- The exact binary-product conjugation table for `x`. -/
theorem basis_conj_x (i : Fin 11) :
    (localX hA hB)⁻¹ * basis hA hB i * localX hA hB =
      binaryProduct (basis hA hB) (fun j => (xMasks i).testBit j.val) := by
  apply representation_injective hA hB
  rw [representation_binaryProduct hA hB (representation_basis hA hB)]
  exact eval_conj (representation hA hB) (representation_basis hA hB i)
    (representation_x hA hB) (matrix_action_x i)

/-- The exact binary-product conjugation table for `y`. -/
theorem basis_conj_y (i : Fin 11) :
    (localY hA hB)⁻¹ * basis hA hB i * localY hA hB =
      binaryProduct (basis hA hB) (fun j => (yMasks i).testBit j.val) := by
  apply representation_injective hA hB
  rw [representation_binaryProduct hA hB (representation_basis hA hB)]
  exact eval_conj (representation hA hB) (representation_basis hA hB i)
    (representation_y hA hB) (matrix_action_y i)

end Janko4.Cardinality.KernelCount
