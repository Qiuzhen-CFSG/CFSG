module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Generators

/-!
# Involutions in normal closures of odd-prime elements of J₁

For each of the five odd prime divisors of the model's order, a product of a
fixed prime-order element with one conjugate has even order. Its half-order
power is an involution. Every asserted matrix identity is checked by kernel
reduction; the finite search and arithmetic generator are untrusted.

The input matrices and ATLAS attribution are in `Model.Basic`. This file is
reproduced by `Source/GenerateOddPrimeWitnesses.py` from those matrices and the
already checked words in `Order.Generators`.
-/

namespace Janko1.OddPrimeWitnesses
open OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem matrixValue_a : matrixValue a = matrixA := rfl
private theorem matrixValue_b : matrixValue b = matrixB := rfl

private theorem inverse_matrix (g : Model) (M D : Mat)
    (h : matrixValue g = M) (hMD : M * D = 1) (hDM : D * M = 1) :
    matrixValue g⁻¹ = D := by
  let u : Ambient := ⟨M, D, hMD, hDM⟩
  have hu : inclusion g = u := Units.ext h
  change (inclusion g⁻¹).val = D
  rw [map_inv, hu]
  rfl

private def T1 : Mat := !![9, 9, 2, 1, 3, 8, 6;
    2, 5, 5, 9, 2, 2, 1;
    5, 9, 9, 9, 8, 10, 3;
    5, 5, 7, 10, 9, 2, 5;
    7, 1, 5, 3, 5, 8, 2;
    6, 9, 10, 1, 10, 2, 3;
    1, 9, 6, 5, 9, 5, 4]

private theorem syllable1 : matrixValue (a * b ^ 1) = T1 := by
  change matrixA * matrixB ^ 1 = T1
  decide +kernel

private def T2 : Mat := !![1, 10, 3, 9, 10, 9, 6;
    5, 9, 4, 9, 6, 6, 1;
    9, 3, 6, 9, 10, 3, 9;
    5, 9, 10, 6, 9, 2, 9;
    9, 3, 8, 2, 9, 10, 6;
    4, 9, 5, 5, 1, 9, 5;
    5, 6, 9, 10, 3, 8, 4]

private theorem syllable2 : matrixValue (a * b ^ 2) = T2 := by
  change matrixA * matrixB ^ 2 = T2
  decide +kernel

private def R3 : Mat := !![5, 7, 1, 8, 5, 8, 2;
    10, 4, 10, 0, 3, 3, 8;
    5, 10, 8, 9, 1, 2, 1;
    2, 3, 3, 6, 1, 2, 9;
    7, 4, 7, 2, 10, 7, 3;
    3, 9, 0, 4, 2, 3, 5;
    3, 4, 3, 3, 9, 4, 9]

private theorem rep3_matrix : matrixValue (b) = R3 := by
  simp only [matrixValue_b]
  decide +kernel

private def c3 : Model := (a * b ^ 1) * (a * b ^ 1) * (a * b ^ 2) * (a * b ^ 1)

private def C3_1 : Mat := !![2, 3, 10, 0, 10, 6, 7;
    4, 8, 8, 8, 0, 9, 3;
    8, 0, 5, 9, 1, 1, 4;
    0, 2, 10, 3, 6, 10, 7;
    3, 3, 4, 3, 4, 4, 5;
    3, 7, 0, 3, 2, 3, 8;
    3, 3, 2, 7, 3, 0, 8]

private theorem c3_step1 : T1 * T1 = C3_1 := by decide +kernel

private def C3_2 : Mat := !![3, 5, 9, 2, 2, 1, 3;
    9, 10, 2, 6, 5, 9, 2;
    10, 3, 6, 9, 2, 2, 3;
    2, 5, 6, 5, 4, 1, 2;
    3, 9, 7, 10, 5, 3, 5;
    2, 3, 5, 9, 1, 10, 1;
    6, 7, 1, 2, 6, 5, 9]

private theorem c3_step2 : C3_1 * T2 = C3_2 := by decide +kernel

private def C3_3 : Mat := !![5, 5, 10, 6, 2, 7, 2;
    1, 8, 2, 2, 8, 5, 2;
    2, 9, 2, 6, 2, 1, 5;
    9, 10, 6, 9, 3, 8, 2;
    1, 9, 5, 4, 9, 5, 5;
    8, 3, 7, 6, 5, 2, 1;
    10, 9, 6, 1, 10, 3, 9]

private theorem c3_step3 : C3_2 * T1 = C3_3 := by decide +kernel

private theorem c3_matrix : matrixValue c3 = C3_3 := by
  have h1 : matrixValue a * matrixValue (b ^ 1) = T1 := syllable1
  have h2 : matrixValue a * matrixValue (b ^ 2) = T2 := syllable2
  simp only [c3, map_mul, h1, h2]
  rw [c3_step1, c3_step2, c3_step3]

private def D3 : Mat := !![5, 1, 2, 9, 1, 8, 10;
    5, 8, 9, 10, 9, 3, 9;
    10, 2, 2, 6, 5, 7, 6;
    6, 2, 6, 9, 4, 6, 1;
    2, 8, 2, 3, 9, 5, 10;
    7, 5, 1, 8, 5, 2, 3;
    2, 2, 5, 2, 5, 1, 9]

private theorem c3_inv_matrix : matrixValue c3⁻¹ = D3 :=
  inverse_matrix _ _ _ c3_matrix (by decide +kernel) (by decide +kernel)

private def V3 : Mat := !![8, 4, 9, 5, 10, 6, 8;
    5, 5, 3, 1, 7, 2, 3;
    5, 5, 0, 9, 8, 1, 5;
    4, 8, 9, 5, 7, 6, 4;
    2, 2, 1, 8, 1, 0, 2;
    4, 1, 1, 4, 8, 8, 2;
    7, 3, 2, 8, 2, 5, 0]

private def W3 : Mat := !![5, 6, 9, 1, 8, 4, 3;
    2, 3, 8, 5, 2, 9, 10;
    2, 0, 10, 8, 0, 9, 7;
    3, 10, 1, 6, 0, 2, 4;
    9, 2, 1, 4, 9, 0, 4;
    8, 1, 8, 9, 10, 1, 3;
    10, 4, 3, 3, 7, 4, 0]

private def Z3 : Mat := !![3, 9, 2, 10, 6, 2, 3;
    2, 1, 8, 8, 4, 6, 6;
    4, 9, 6, 5, 10, 5, 2;
    1, 5, 2, 2, 9, 6, 9;
    5, 5, 1, 2, 6, 4, 2;
    3, 9, 10, 2, 5, 1, 1;
    6, 9, 10, 8, 2, 9, 8]

private def J3 : Mat := !![1, 4, 6, 9, 3, 8, 5;
    4, 0, 2, 1, 2, 7, 9;
    6, 2, 2, 3, 2, 10, 3;
    9, 1, 3, 8, 1, 8, 10;
    3, 2, 2, 1, 0, 7, 0;
    8, 7, 10, 8, 7, 0, 4;
    5, 9, 3, 10, 0, 4, 10]

private theorem product3_step1 : R3 * C3_3 = V3 := by decide +kernel
private theorem product3_step2 : V3 * R3 = W3 := by decide +kernel
private theorem product3_step3 : W3 * D3 = Z3 := by decide +kernel
private theorem product3_power : Z3 ^ 5 = J3 := by decide +kernel

private theorem witness3_matrix :
    matrixValue (((b) * c3 * (b) * c3⁻¹) ^ 5) = J3 := by
  calc
    _ = (matrixValue (b) * matrixValue c3 * matrixValue (b) *
        matrixValue c3⁻¹) ^ 5 := by simp only [map_mul, map_pow]
    _ = J3 := by
      rw [rep3_matrix, c3_matrix, c3_inv_matrix,
        product3_step1, product3_step2, product3_step3, product3_power]

/-- A normal subgroup containing the chosen element of order 3 contains an involution. -/
public theorem involution_of_3_mem (N : Subgroup Model) [hN : N.Normal]
    (hr : (b) ∈ N) : ∃ z : N, orderOf z = 2 := by
  let z : N := ⟨((b) * c3 * (b) * c3⁻¹) ^ 5, N.pow_mem (by
    simpa only [mul_assoc] using N.mul_mem hr (hN.conj_mem _ hr c3)) 5⟩
  refine ⟨z, ?_⟩
  rw [← Subgroup.orderOf_coe]
  have hp : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixValue_injective
    change matrixValue ((z : Model) ^ 2) = matrixValue 1
    rw [map_pow, map_one]
    change matrixValue (((b) * c3 * (b) * c3⁻¹) ^ 5) ^ 2 = 1
    rw [witness3_matrix]
    decide +kernel
  · intro he
    have hm := congrArg matrixValue he
    change matrixValue (((b) * c3 * (b) * c3⁻¹) ^ 5) = matrixValue 1 at hm
    rw [witness3_matrix, map_one] at hm
    exact (by decide +kernel : J3 ≠ 1) hm

private def R5 : Mat := !![5, 8, 0, 1, 2, 1, 4;
    7, 2, 9, 9, 0, 1, 4;
    2, 3, 10, 10, 1, 8, 3;
    3, 10, 4, 4, 7, 8, 0;
    1, 5, 3, 6, 7, 2, 8;
    6, 9, 2, 8, 9, 8, 10;
    8, 2, 0, 0, 2, 1, 4]

private theorem rep5_matrix : matrixValue (x * y) = R5 := by
  simp only [map_mul, matrixValue_x, matrixValue_y]
  decide +kernel

private def c5 : Model := (a * b ^ 2)

private theorem c5_matrix : matrixValue c5 = T2 := by
  have h1 : matrixValue a * matrixValue (b ^ 1) = T1 := syllable1
  have h2 : matrixValue a * matrixValue (b ^ 2) = T2 := syllable2
  simp only [c5, map_mul, h2]

private def D5 : Mat := !![1, 5, 9, 5, 9, 4, 5;
    10, 9, 3, 9, 3, 9, 6;
    3, 4, 6, 10, 8, 5, 9;
    9, 9, 9, 6, 2, 5, 10;
    10, 6, 10, 9, 9, 1, 3;
    9, 6, 3, 2, 10, 9, 8;
    6, 1, 9, 9, 6, 5, 4]

private theorem c5_inv_matrix : matrixValue c5⁻¹ = D5 :=
  inverse_matrix _ _ _ c5_matrix (by decide +kernel) (by decide +kernel)

private def V5 : Mat := !![4, 5, 4, 7, 6, 2, 3;
    2, 9, 5, 8, 2, 7, 7;
    4, 7, 0, 3, 1, 5, 0;
    6, 8, 0, 0, 6, 7, 6;
    7, 7, 8, 1, 4, 3, 0;
    8, 4, 7, 7, 6, 9, 5;
    5, 5, 1, 7, 2, 2, 6]

private def W5 : Mat := !![5, 2, 3, 4, 6, 7, 7;
    9, 7, 7, 2, 2, 6, 8;
    10, 5, 0, 4, 4, 0, 3;
    6, 4, 5, 5, 8, 0, 0;
    4, 8, 0, 4, 7, 8, 10;
    5, 9, 5, 8, 7, 4, 7;
    2, 9, 5, 6, 5, 1, 4]

private def Z5 : Mat := !![4, 0, 7, 8, 7, 1, 8;
    9, 1, 8, 6, 2, 9, 3;
    0, 4, 10, 6, 2, 3, 1;
    10, 3, 1, 9, 1, 8, 8;
    3, 8, 5, 10, 7, 6, 2;
    0, 7, 0, 8, 9, 2, 10;
    2, 7, 9, 7, 0, 2, 10]

private def J5 : Mat := !![10, 5, 6, 6, 6, 4, 7;
    5, 0, 7, 4, 8, 8, 5;
    6, 7, 6, 10, 6, 5, 4;
    6, 4, 10, 6, 6, 7, 5;
    6, 8, 6, 6, 8, 8, 8;
    4, 8, 5, 7, 8, 5, 0;
    7, 5, 4, 5, 8, 0, 8]

private theorem product5_step1 : R5 * T2 = V5 := by decide +kernel
private theorem product5_step2 : V5 * R5 = W5 := by decide +kernel
private theorem product5_step3 : W5 * D5 = Z5 := by decide +kernel
private theorem product5_power : Z5 ^ 3 = J5 := by decide +kernel

private theorem witness5_matrix :
    matrixValue (((x * y) * c5 * (x * y) * c5⁻¹) ^ 3) = J5 := by
  calc
    _ = (matrixValue (x * y) * matrixValue c5 * matrixValue (x * y) *
        matrixValue c5⁻¹) ^ 3 := by simp only [map_mul, map_pow]
    _ = J5 := by
      rw [rep5_matrix, c5_matrix, c5_inv_matrix,
        product5_step1, product5_step2, product5_step3, product5_power]

/-- A normal subgroup containing the chosen element of order 5 contains an involution. -/
public theorem involution_of_5_mem (N : Subgroup Model) [hN : N.Normal]
    (hr : (x * y) ∈ N) : ∃ z : N, orderOf z = 2 := by
  let z : N := ⟨((x * y) * c5 * (x * y) * c5⁻¹) ^ 3, N.pow_mem (by
    simpa only [mul_assoc] using N.mul_mem hr (hN.conj_mem _ hr c5)) 3⟩
  refine ⟨z, ?_⟩
  rw [← Subgroup.orderOf_coe]
  have hp : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixValue_injective
    change matrixValue ((z : Model) ^ 2) = matrixValue 1
    rw [map_pow, map_one]
    change matrixValue (((x * y) * c5 * (x * y) * c5⁻¹) ^ 3) ^ 2 = 1
    rw [witness5_matrix]
    decide +kernel
  · intro he
    have hm := congrArg matrixValue he
    change matrixValue (((x * y) * c5 * (x * y) * c5⁻¹) ^ 3) = matrixValue 1 at hm
    rw [witness5_matrix, map_one] at hm
    exact (by decide +kernel : J5 ≠ 1) hm

private def R7 : Mat := !![9, 9, 2, 1, 3, 8, 6;
    2, 5, 5, 9, 2, 2, 1;
    5, 9, 9, 9, 8, 10, 3;
    5, 5, 7, 10, 9, 2, 5;
    7, 1, 5, 3, 5, 8, 2;
    6, 9, 10, 1, 10, 2, 3;
    1, 9, 6, 5, 9, 5, 4]

private theorem rep7_matrix : matrixValue (a * b) = R7 := by
  simp only [map_mul, matrixValue_a, matrixValue_b]
  decide +kernel

private def c7 : Model := (a * b ^ 2) * (a * b ^ 1) * (a * b ^ 2)

private def C7_1 : Mat := !![10, 1, 10, 2, 3, 6, 9;
    9, 9, 8, 10, 3, 5, 9;
    6, 5, 9, 5, 4, 1, 9;
    7, 10, 9, 2, 5, 5, 5;
    2, 1, 3, 8, 6, 9, 9;
    5, 3, 5, 8, 2, 7, 1;
    5, 9, 2, 2, 1, 2, 5]

private theorem c7_step1 : T2 * T1 = C7_1 := by decide +kernel

private def C7_2 : Mat := !![2, 10, 7, 8, 9, 0, 0;
    4, 8, 0, 8, 10, 7, 7;
    2, 10, 7, 5, 3, 0, 1;
    7, 9, 3, 1, 6, 3, 6;
    0, 10, 7, 7, 9, 9, 9;
    2, 8, 10, 5, 9, 9, 3;
    10, 8, 3, 9, 3, 1, 1]

private theorem c7_step2 : C7_1 * T2 = C7_2 := by decide +kernel

private theorem c7_matrix : matrixValue c7 = C7_2 := by
  have h1 : matrixValue a * matrixValue (b ^ 1) = T1 := syllable1
  have h2 : matrixValue a * matrixValue (b ^ 2) = T2 := syllable2
  simp only [c7, map_mul, h1, h2]
  rw [c7_step1, c7_step2]

private def D7 : Mat := !![2, 4, 2, 7, 0, 2, 10;
    10, 8, 10, 9, 10, 8, 8;
    7, 0, 7, 3, 7, 10, 3;
    8, 8, 5, 1, 7, 5, 9;
    9, 10, 3, 6, 9, 9, 3;
    0, 7, 0, 3, 9, 9, 1;
    0, 7, 1, 6, 9, 3, 1]

private theorem c7_inv_matrix : matrixValue c7⁻¹ = D7 :=
  inverse_matrix _ _ _ c7_matrix (by decide +kernel) (by decide +kernel)

private def V7 : Mat := !![9, 3, 1, 6, 3, 6, 7;
    1, 4, 3, 2, 0, 0, 9;
    1, 4, 4, 2, 2, 2, 0;
    3, 0, 3, 1, 4, 4, 7;
    8, 10, 5, 9, 9, 3, 2;
    10, 7, 5, 3, 0, 1, 2;
    3, 8, 2, 8, 10, 10, 1]

private def W7 : Mat := !![10, 2, 3, 1, 2, 6, 10;
    7, 4, 7, 8, 2, 7, 10;
    7, 7, 3, 2, 3, 3, 9;
    7, 8, 10, 3, 0, 10, 3;
    3, 2, 8, 9, 5, 9, 10;
    9, 3, 0, 5, 7, 8, 9;
    4, 3, 1, 9, 8, 5, 5]

private def Z7 : Mat := !![10, 9, 5, 1, 1, 8, 2;
    9, 10, 5, 9, 8, 3, 9;
    5, 5, 1, 6, 9, 4, 9;
    1, 9, 6, 4, 2, 6, 6;
    1, 8, 9, 2, 3, 6, 9;
    8, 3, 4, 6, 6, 9, 10;
    2, 9, 9, 6, 9, 10, 6]

private def J7 : Mat := !![10, 9, 5, 1, 1, 8, 2;
    9, 10, 5, 9, 8, 3, 9;
    5, 5, 1, 6, 9, 4, 9;
    1, 9, 6, 4, 2, 6, 6;
    1, 8, 9, 2, 3, 6, 9;
    8, 3, 4, 6, 6, 9, 10;
    2, 9, 9, 6, 9, 10, 6]

private theorem product7_step1 : R7 * C7_2 = V7 := by decide +kernel
private theorem product7_step2 : V7 * R7 = W7 := by decide +kernel
private theorem product7_step3 : W7 * D7 = Z7 := by decide +kernel
private theorem product7_power : Z7 ^ 1 = J7 := by decide +kernel

private theorem witness7_matrix :
    matrixValue (((a * b) * c7 * (a * b) * c7⁻¹) ^ 1) = J7 := by
  calc
    _ = (matrixValue (a * b) * matrixValue c7 * matrixValue (a * b) *
        matrixValue c7⁻¹) ^ 1 := by simp only [map_mul, map_pow]
    _ = J7 := by
      rw [rep7_matrix, c7_matrix, c7_inv_matrix,
        product7_step1, product7_step2, product7_step3, product7_power]

/-- A normal subgroup containing the chosen element of order 7 contains an involution. -/
public theorem involution_of_7_mem (N : Subgroup Model) [hN : N.Normal]
    (hr : (a * b) ∈ N) : ∃ z : N, orderOf z = 2 := by
  let z : N := ⟨((a * b) * c7 * (a * b) * c7⁻¹) ^ 1, N.pow_mem (by
    simpa only [mul_assoc] using N.mul_mem hr (hN.conj_mem _ hr c7)) 1⟩
  refine ⟨z, ?_⟩
  rw [← Subgroup.orderOf_coe]
  have hp : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixValue_injective
    change matrixValue ((z : Model) ^ 2) = matrixValue 1
    rw [map_pow, map_one]
    change matrixValue (((a * b) * c7 * (a * b) * c7⁻¹) ^ 1) ^ 2 = 1
    rw [witness7_matrix]
    decide +kernel
  · intro he
    have hm := congrArg matrixValue he
    change matrixValue (((a * b) * c7 * (a * b) * c7⁻¹) ^ 1) = matrixValue 1 at hm
    rw [witness7_matrix, map_one] at hm
    exact (by decide +kernel : J7 ≠ 1) hm

private def R11 : Mat := !![7, 0, 7, 2, 0, 7, 2;
    2, 9, 4, 0, 0, 7, 4;
    10, 7, 1, 4, 7, 7, 10;
    2, 7, 1, 9, 4, 10, 6;
    1, 7, 6, 7, 9, 1, 9;
    7, 0, 2, 0, 2, 4, 4;
    5, 9, 2, 4, 4, 1, 1]

private theorem rep11_matrix : matrixValue (x * y ^ 2) = R11 := by
  simp only [map_mul, map_pow, matrixValue_x, matrixValue_y]
  decide +kernel

private def c11 : Model := (a * b ^ 2)

private theorem c11_matrix : matrixValue c11 = T2 := by
  have h1 : matrixValue a * matrixValue (b ^ 1) = T1 := syllable1
  have h2 : matrixValue a * matrixValue (b ^ 2) = T2 := syllable2
  simp only [c11, map_mul, h2]

private def D11 : Mat := !![1, 5, 9, 5, 9, 4, 5;
    10, 9, 3, 9, 3, 9, 6;
    3, 4, 6, 10, 8, 5, 9;
    9, 9, 9, 6, 2, 5, 10;
    10, 6, 10, 9, 9, 1, 3;
    9, 6, 3, 2, 10, 9, 8;
    6, 1, 9, 9, 6, 5, 4]

private theorem c11_inv_matrix : matrixValue c11⁻¹ = D11 :=
  inverse_matrix _ _ _ c11_matrix (by decide +kernel) (by decide +kernel)

private def V11 : Mat := !![8, 8, 4, 6, 6, 2, 1;
    10, 2, 5, 1, 1, 3, 9;
    6, 5, 10, 5, 2, 4, 9;
    10, 8, 2, 9, 8, 6, 9;
    2, 2, 9, 6, 9, 1, 5;
    2, 10, 6, 2, 3, 3, 9;
    1, 2, 6, 4, 2, 5, 5]

private def W11 : Mat := !![6, 6, 8, 0, 4, 6, 0;
    6, 5, 4, 4, 2, 8, 4;
    6, 3, 5, 4, 9, 4, 7;
    10, 0, 4, 3, 5, 7, 0;
    7, 0, 4, 1, 3, 4, 8;
    2, 6, 5, 4, 9, 5, 10;
    9, 4, 2, 8, 7, 9, 5]

private def Z11 : Mat := !![8, 0, 2, 3, 1, 0, 0;
    0, 4, 0, 0, 0, 5, 2;
    2, 0, 8, 8, 10, 0, 0;
    8, 0, 3, 2, 1, 0, 0;
    10, 0, 1, 1, 3, 0, 0;
    0, 5, 0, 0, 0, 2, 7;
    0, 9, 0, 0, 0, 4, 5]

private def J11 : Mat := !![10, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 10, 0, 0, 0, 0;
    0, 0, 0, 10, 0, 0, 0;
    0, 0, 0, 0, 10, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

private theorem product11_step1 : R11 * T2 = V11 := by decide +kernel
private theorem product11_step2 : V11 * R11 = W11 := by decide +kernel
private theorem product11_step3 : W11 * D11 = Z11 := by decide +kernel
private theorem product11_power : Z11 ^ 3 = J11 := by decide +kernel

private theorem witness11_matrix :
    matrixValue (((x * y ^ 2) * c11 * (x * y ^ 2) * c11⁻¹) ^ 3) = J11 := by
  calc
    _ = (matrixValue (x * y ^ 2) * matrixValue c11 * matrixValue (x * y ^ 2) *
        matrixValue c11⁻¹) ^ 3 := by simp only [map_mul, map_pow]
    _ = J11 := by
      rw [rep11_matrix, c11_matrix, c11_inv_matrix,
        product11_step1, product11_step2, product11_step3, product11_power]

/-- A normal subgroup containing the chosen element of order 11 contains an involution. -/
public theorem involution_of_11_mem (N : Subgroup Model) [hN : N.Normal]
    (hr : (x * y ^ 2) ∈ N) : ∃ z : N, orderOf z = 2 := by
  let z : N := ⟨((x * y ^ 2) * c11 * (x * y ^ 2) * c11⁻¹) ^ 3, N.pow_mem (by
    simpa only [mul_assoc] using N.mul_mem hr (hN.conj_mem _ hr c11)) 3⟩
  refine ⟨z, ?_⟩
  rw [← Subgroup.orderOf_coe]
  have hp : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixValue_injective
    change matrixValue ((z : Model) ^ 2) = matrixValue 1
    rw [map_pow, map_one]
    change matrixValue (((x * y ^ 2) * c11 * (x * y ^ 2) * c11⁻¹) ^ 3) ^ 2 = 1
    rw [witness11_matrix]
    decide +kernel
  · intro he
    have hm := congrArg matrixValue he
    change matrixValue (((x * y ^ 2) * c11 * (x * y ^ 2) * c11⁻¹) ^ 3) = matrixValue 1 at hm
    rw [witness11_matrix, map_one] at hm
    exact (by decide +kernel : J11 ≠ 1) hm

private def R19 : Mat := !![1, 6, 5, 6, 6, 7, 7;
    5, 4, 5, 10, 6, 6, 4;
    6, 8, 6, 5, 3, 8, 3;
    4, 6, 7, 5, 8, 0, 8;
    5, 0, 7, 7, 3, 8, 6;
    6, 4, 10, 5, 5, 7, 6;
    4, 8, 5, 4, 3, 5, 0]

private theorem rep19_matrix : matrixValue (a * b * a * b ^ 2) = R19 := by
  simp only [map_mul, map_pow, matrixValue_a, matrixValue_b]
  decide +kernel

private def c19 : Model := (a * b ^ 2) * (a * b ^ 1) * (a * b ^ 2) * (a * b ^ 1)

private def C19_1 : Mat := !![10, 1, 10, 2, 3, 6, 9;
    9, 9, 8, 10, 3, 5, 9;
    6, 5, 9, 5, 4, 1, 9;
    7, 10, 9, 2, 5, 5, 5;
    2, 1, 3, 8, 6, 9, 9;
    5, 3, 5, 8, 2, 7, 1;
    5, 9, 2, 2, 1, 2, 5]

private theorem c19_step1 : T2 * T1 = C19_1 := by decide +kernel

private def C19_2 : Mat := !![2, 10, 7, 8, 9, 0, 0;
    4, 8, 0, 8, 10, 7, 7;
    2, 10, 7, 5, 3, 0, 1;
    7, 9, 3, 1, 6, 3, 6;
    0, 10, 7, 7, 9, 9, 9;
    2, 8, 10, 5, 9, 9, 3;
    10, 8, 3, 9, 3, 1, 1]

private theorem c19_step2 : C19_1 * T2 = C19_2 := by decide +kernel

private def C19_3 : Mat := !![0, 4, 9, 9, 1, 7, 2;
    2, 10, 2, 8, 8, 6, 9;
    10, 3, 8, 10, 8, 2, 1;
    2, 7, 2, 0, 10, 3, 0;
    7, 0, 10, 7, 3, 8, 4;
    9, 4, 3, 1, 1, 5, 0;
    7, 3, 5, 5, 9, 10, 3]

private theorem c19_step3 : C19_2 * T1 = C19_3 := by decide +kernel

private theorem c19_matrix : matrixValue c19 = C19_3 := by
  have h1 : matrixValue a * matrixValue (b ^ 1) = T1 := syllable1
  have h2 : matrixValue a * matrixValue (b ^ 2) = T2 := syllable2
  simp only [c19, map_mul, h1, h2]
  rw [c19_step1, c19_step2, c19_step3]

private def D19 : Mat := !![0, 2, 10, 2, 7, 9, 7;
    4, 10, 3, 7, 0, 4, 3;
    9, 2, 8, 2, 10, 3, 5;
    9, 8, 10, 0, 7, 1, 5;
    1, 8, 8, 10, 3, 1, 9;
    7, 6, 2, 3, 8, 5, 10;
    2, 9, 1, 0, 4, 0, 3]

private theorem c19_inv_matrix : matrixValue c19⁻¹ = D19 :=
  inverse_matrix _ _ _ c19_matrix (by decide +kernel) (by decide +kernel)

private def V19 : Mat := !![8, 5, 2, 4, 6, 4, 7;
    4, 5, 2, 8, 6, 8, 10;
    2, 0, 10, 2, 3, 2, 1;
    6, 2, 3, 8, 1, 6, 4;
    10, 8, 1, 9, 4, 7, 3;
    5, 10, 0, 5, 2, 5, 8;
    8, 5, 2, 0, 8, 4, 9]

private def W19 : Mat := !![0, 4, 2, 9, 10, 4, 9;
    4, 0, 10, 4, 3, 8, 4;
    2, 10, 9, 8, 3, 5, 2;
    2, 7, 3, 10, 1, 5, 0;
    1, 8, 8, 1, 8, 2, 1;
    4, 8, 5, 6, 9, 10, 3;
    2, 7, 9, 0, 1, 8, 0]

private def Z19 : Mat := !![6, 4, 6, 1, 5, 6, 4;
    6, 3, 6, 5, 3, 3, 8;
    4, 5, 7, 5, 8, 0, 3;
    5, 0, 7, 7, 3, 3, 5;
    5, 4, 1, 6, 6, 7, 6;
    7, 8, 6, 7, 8, 5, 0;
    1, 5, 5, 6, 6, 4, 4]

private def J19 : Mat := !![4, 6, 9, 3, 6, 8, 1;
    6, 10, 0, 5, 9, 6, 8;
    9, 0, 10, 2, 8, 9, 1;
    3, 5, 2, 0, 3, 7, 9;
    6, 9, 8, 3, 1, 6, 7;
    8, 6, 9, 7, 6, 4, 4;
    1, 8, 1, 9, 7, 4, 3]

private theorem product19_step1 : R19 * C19_3 = V19 := by decide +kernel
private theorem product19_step2 : V19 * R19 = W19 := by decide +kernel
private theorem product19_step3 : W19 * D19 = Z19 := by decide +kernel
private theorem product19_power : Z19 ^ 5 = J19 := by decide +kernel

private theorem witness19_matrix :
    matrixValue (((a * b * a * b ^ 2) * c19 * (a * b * a * b ^ 2) * c19⁻¹) ^ 5) = J19 := by
  calc
    _ = (matrixValue (a * b * a * b ^ 2) * matrixValue c19 * matrixValue (a * b * a * b ^ 2) *
        matrixValue c19⁻¹) ^ 5 := by simp only [map_mul, map_pow]
    _ = J19 := by
      rw [rep19_matrix, c19_matrix, c19_inv_matrix,
        product19_step1, product19_step2, product19_step3, product19_power]

/-- A normal subgroup containing the chosen element of order 19 contains an involution. -/
public theorem involution_of_19_mem (N : Subgroup Model) [hN : N.Normal]
    (hr : (a * b * a * b ^ 2) ∈ N) : ∃ z : N, orderOf z = 2 := by
  let z : N := ⟨((a * b * a * b ^ 2) * c19 * (a * b * a * b ^ 2) * c19⁻¹) ^ 5, N.pow_mem (by
    simpa only [mul_assoc] using N.mul_mem hr (hN.conj_mem _ hr c19)) 5⟩
  refine ⟨z, ?_⟩
  rw [← Subgroup.orderOf_coe]
  have hp : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply matrixValue_injective
    change matrixValue ((z : Model) ^ 2) = matrixValue 1
    rw [map_pow, map_one]
    change matrixValue (((a * b * a * b ^ 2) * c19 * (a * b * a * b ^ 2) * c19⁻¹) ^ 5) ^ 2 = 1
    rw [witness19_matrix]
    decide +kernel
  · intro he
    have hm := congrArg matrixValue he
    change matrixValue (((a * b * a * b ^ 2) * c19 * (a * b * a * b ^ 2) * c19⁻¹) ^ 5) = matrixValue 1 at hm
    rw [witness19_matrix, map_one] at hm
    exact (by decide +kernel : J19 ≠ 1) hm

end Janko1.OddPrimeWitnesses
