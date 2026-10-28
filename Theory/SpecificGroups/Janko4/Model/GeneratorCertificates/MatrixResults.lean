module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Products
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NormNum
/-!
# Orders of the ATLAS J4 matrices

The packed products certify A² = B⁴ = (AB)³⁷ = (ABABB)¹⁰ = I.
Entries of A, B², AB, (ABABB)² and (ABABB)⁵ distinguish them from I,
so prime-divisor tests prove that these orders are exact. The generator
convention and source are documented in `Model.Data`.
-/

public section
namespace Janko4
open GeneratorCertificates

lemma matrixA_mul_self : matrixA * matrixA = 1 := by
  rw [matrixA, ← decode_packedMul, product_a_a, decode_packedOne]
private lemma decode_b2 : decodeRows b2Rows = matrixB ^ 2 := by
  rw [← product_b_b, decode_packedMul, pow_two]
  rfl
lemma matrixB_pow_four : matrixB ^ 4 = 1 := by
  have h := congrArg decodeRows product_b2_b2
  rw [decode_packedMul, decode_b2, ← pow_add, decode_packedOne] at h
  exact h
private lemma decode_c : decodeRows cRows = matrixA * matrixB := by
  rw [← product_a_b, decode_packedMul]
  rfl
private lemma decode_c2 : decodeRows c2Rows = (matrixA * matrixB) ^ 2 := by
  rw [← product_c_c, decode_packedMul, decode_c, pow_two]
private lemma decode_c4 : decodeRows c4Rows = (matrixA * matrixB) ^ 4 := by
  rw [← product_c2_c2, decode_packedMul, decode_c2, ← pow_add]
private lemma decode_c8 : decodeRows c8Rows = (matrixA * matrixB) ^ 8 := by
  rw [← product_c4_c4, decode_packedMul, decode_c4, ← pow_add]
private lemma decode_c16 : decodeRows c16Rows = (matrixA * matrixB) ^ 16 := by
  rw [← product_c8_c8, decode_packedMul, decode_c8, ← pow_add]
private lemma decode_c32 : decodeRows c32Rows = (matrixA * matrixB) ^ 32 := by
  rw [← product_c16_c16, decode_packedMul, decode_c16, ← pow_add]
private lemma decode_c36 : decodeRows c36Rows = (matrixA * matrixB) ^ 36 := by
  rw [← product_c32_c4, decode_packedMul, decode_c32, decode_c4, ← pow_add]
lemma matrixAB_pow_37 : (matrixA * matrixB) ^ 37 = 1 := by
  have h := congrArg decodeRows product_c36_c
  rw [decode_packedMul, decode_c36, decode_c, ← pow_succ, decode_packedOne] at h
  exact h
private lemma decode_d : decodeRows dRows = matrixA * matrixB * matrixA * matrixB * matrixB := by
  rw [← product_c2_b, decode_packedMul, decode_c2, pow_two]
  simp only [matrixB, mul_assoc]
private lemma decode_d2 : decodeRows d2Rows = (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 2 := by
  rw [← product_d_d, decode_packedMul, decode_d, pow_two]
private lemma decode_d4 : decodeRows d4Rows = (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 4 := by
  rw [← product_d2_d2, decode_packedMul, decode_d2, ← pow_add]
private lemma decode_d5 : decodeRows d5Rows = (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 5 := by
  rw [← product_d4_d, decode_packedMul, decode_d4, decode_d, ← pow_succ]
lemma matrixABABB_pow_ten : (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 10 = 1 := by
  have h := congrArg decodeRows product_d5_d5
  rw [decode_packedMul, decode_d5, ← pow_add, decode_packedOne] at h
  exact h

lemma matrixA_ne_one : matrixA ≠ 1 := by
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 0) h
  have h0 : matrixA 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
  exact h0 e
lemma matrixB_sq_ne_one : matrixB ^ 2 ≠ 1 := by
  rw [← decode_b2]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 2) h
  have h0 : decodeRows b2Rows 0 2 ≠ (1 : BinaryMatrix) 0 2 := by decide +kernel
  exact h0 e
lemma matrixAB_ne_one : matrixA * matrixB ≠ 1 := by
  rw [← decode_c]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 0) h
  have h0 : decodeRows cRows 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
  exact h0 e
lemma matrixABABB_sq_ne_one : (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 2 ≠ 1 := by
  rw [← decode_d2]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 2) h
  have h0 : decodeRows d2Rows 0 2 ≠ (1 : BinaryMatrix) 0 2 := by decide +kernel
  exact h0 e
lemma matrixABABB_pow_five_ne_one : (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 5 ≠ 1 := by
  rw [← decode_d5]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 0) h
  have h0 : decodeRows d5Rows 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
  exact h0 e

lemma orderOf_matrixA : orderOf matrixA = 2 :=
  orderOf_eq_prime (by simpa only [pow_two] using matrixA_mul_self) matrixA_ne_one
lemma orderOf_matrixB : orderOf matrixB = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) matrixB_sq_ne_one matrixB_pow_four
lemma orderOf_matrixAB : orderOf (matrixA * matrixB) = 37 := by
  let : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact orderOf_eq_prime matrixAB_pow_37 matrixAB_ne_one
lemma orderOf_matrixABABB : orderOf (matrixA * matrixB * matrixA * matrixB * matrixB) = 10 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) matrixABABB_pow_ten
  intro p hp hd
  have h : p = 2 ∨ p = 5 := by
    have : p ∣ 2 ∨ p ∣ 5 := (hp.dvd_mul).mp hd
    exact this.imp (fun h => ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp h).symm)
      (fun h => ((Nat.prime_five.dvd_iff_eq hp.ne_one).mp h).symm)
  rcases h with rfl | rfl
  · exact matrixABABB_pow_five_ne_one
  · exact matrixABABB_sq_ne_one
end Janko4
