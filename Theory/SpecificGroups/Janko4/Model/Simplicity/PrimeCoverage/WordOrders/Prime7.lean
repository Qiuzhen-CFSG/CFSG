module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime7Products

/-!
# Kernel-checked power products for the J4 word of order 7

Packed rows are witnesses only: the accompanying products are checked by the
Lean kernel and decoded using `decode_packedMul`. The words and bit convention
come from `Model.Simplicity.Words` and `Model.Data`, following
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates

@[expose] def matrixWord7 : BinaryMatrix := (matrixB * (((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))))

lemma decode_p7e1 : decodeRows t9Rows = matrixWord7 ^ 1 := by
  simpa only [pow_one, matrixWord7] using decode_t9

lemma decode_p7e2 : decodeRows p7e2Rows = matrixWord7 ^ 2 := by
  have h := congrArg decodeRows product_p7e2
  rw [decode_packedMul, decode_p7e1, ← pow_add] at h
  exact h.symm

lemma decode_p7e3 : decodeRows p7e3Rows = matrixWord7 ^ 3 := by
  have h := congrArg decodeRows product_p7e3
  rw [decode_packedMul, decode_p7e2, decode_p7e1, ← pow_add] at h
  exact h.symm

lemma decode_p7e6 : decodeRows p7e6Rows = matrixWord7 ^ 6 := by
  have h := congrArg decodeRows product_p7e6
  rw [decode_packedMul, decode_p7e3, ← pow_add] at h
  exact h.symm

lemma decode_p7e4 : decodeRows p7e4Rows = matrixWord7 ^ 4 := by
  have h := congrArg decodeRows product_p7e4
  rw [decode_packedMul, decode_p7e2, ← pow_add] at h
  exact h.symm

lemma decode_p7e5 : decodeRows p7e5Rows = matrixWord7 ^ 5 := by
  have h := congrArg decodeRows product_p7e5
  rw [decode_packedMul, decode_p7e4, decode_p7e1, ← pow_add] at h
  exact h.symm

lemma decode_p7e10 : decodeRows p7e10Rows = matrixWord7 ^ 10 := by
  have h := congrArg decodeRows product_p7e10
  rw [decode_packedMul, decode_p7e5, ← pow_add] at h
  exact h.symm

lemma decode_p7e20 : decodeRows p7e20Rows = matrixWord7 ^ 20 := by
  have h := congrArg decodeRows product_p7e20
  rw [decode_packedMul, decode_p7e10, ← pow_add] at h
  exact h.symm

lemma decode_p7e21 : decodeRows p7e21Rows = matrixWord7 ^ 21 := by
  have h := congrArg decodeRows product_p7e21
  rw [decode_packedMul, decode_p7e20, decode_p7e1, ← pow_add] at h
  exact h.symm

lemma decode_p7e42 : 1 = matrixWord7 ^ 42 := by
  have h := congrArg decodeRows product_p7e42
  rw [decode_packedMul, decode_p7e21, ← pow_add, decode_packedOne] at h
  exact h.symm

lemma matrixWord7_representative_ne_one : matrixWord7 ^ 6 ≠ 1 := by
  rw [← decode_p7e6]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 0) h
  have h0 : decodeRows p7e6Rows 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
  exact h0 e

lemma orderOf_matrixWord7_representative : orderOf (matrixWord7 ^ 6) = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime _ matrixWord7_representative_ne_one
  rw [← pow_mul]
  exact decode_p7e42.symm

end Janko4.Simplicity.WordOrderCertificates
