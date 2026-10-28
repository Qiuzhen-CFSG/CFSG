module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime29Products

/-!
# Kernel-checked power products for the J4 word of order 29

Packed rows are witnesses only: the accompanying products are checked by the
Lean kernel and decoded using `decode_packedMul`. The words and bit convention
come from `Model.Simplicity.Words` and `Model.Data`, following
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates

@[expose] def matrixWord29 : BinaryMatrix := ((matrixA * matrixB) * (matrixB * (matrixA * ((matrixA * matrixB * matrixA * matrixB * matrixB) * ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB))))))))

lemma decode_p29e1 : decodeRows t6Rows = matrixWord29 ^ 1 := by
  simpa only [pow_one, matrixWord29] using decode_t6

lemma decode_p29e2 : decodeRows p29e2Rows = matrixWord29 ^ 2 := by
  have h := congrArg decodeRows product_p29e2
  rw [decode_packedMul, decode_p29e1, ← pow_add] at h
  exact h.symm

lemma decode_p29e3 : decodeRows p29e3Rows = matrixWord29 ^ 3 := by
  have h := congrArg decodeRows product_p29e3
  rw [decode_packedMul, decode_p29e2, decode_p29e1, ← pow_add] at h
  exact h.symm

lemma decode_p29e6 : decodeRows p29e6Rows = matrixWord29 ^ 6 := by
  have h := congrArg decodeRows product_p29e6
  rw [decode_packedMul, decode_p29e3, ← pow_add] at h
  exact h.symm

lemma decode_p29e7 : decodeRows p29e7Rows = matrixWord29 ^ 7 := by
  have h := congrArg decodeRows product_p29e7
  rw [decode_packedMul, decode_p29e6, decode_p29e1, ← pow_add] at h
  exact h.symm

lemma decode_p29e14 : decodeRows p29e14Rows = matrixWord29 ^ 14 := by
  have h := congrArg decodeRows product_p29e14
  rw [decode_packedMul, decode_p29e7, ← pow_add] at h
  exact h.symm

lemma decode_p29e28 : decodeRows p29e28Rows = matrixWord29 ^ 28 := by
  have h := congrArg decodeRows product_p29e28
  rw [decode_packedMul, decode_p29e14, ← pow_add] at h
  exact h.symm

lemma decode_p29e29 : 1 = matrixWord29 ^ 29 := by
  have h := congrArg decodeRows product_p29e29
  rw [decode_packedMul, decode_p29e28, decode_p29e1, ← pow_add, decode_packedOne] at h
  exact h.symm

lemma matrixWord29_representative_ne_one : matrixWord29 ^ 1 ≠ 1 := by
  rw [← decode_p29e1]
  intro h
  have e := congrArg (fun m : BinaryMatrix => m 0 0) h
  have h0 : decodeRows t6Rows 0 0 ≠ (1 : BinaryMatrix) 0 0 := by decide +kernel
  exact h0 e

lemma orderOf_matrixWord29_representative : orderOf (matrixWord29 ^ 1) = 29 := by
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  apply orderOf_eq_prime _ matrixWord29_representative_ne_one
  rw [← pow_mul]
  exact decode_p29e29.symm

end Janko4.Simplicity.WordOrderCertificates
