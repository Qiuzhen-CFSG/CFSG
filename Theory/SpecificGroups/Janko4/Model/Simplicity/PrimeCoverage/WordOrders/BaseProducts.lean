module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.BaseTables
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Products

/-!
# Certified products evaluating the additional J4 words

Packed rows are witnesses only: the accompanying products are checked by the
Lean kernel and decoded using `decode_packedMul`. The words and bit convention
come from `Model.Simplicity.Words` and `Model.Data`, following
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_t0 : packedMul cRows dRows = t0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t1 : packedMul bRows t0Rows = t1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t2 : packedMul cRows t1Rows = t2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t3 : packedMul dRows t2Rows = t3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t4 : packedMul aRows t3Rows = t4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t5 : packedMul bRows t4Rows = t5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t6 : packedMul cRows t5Rows = t6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t7 : packedMul dRows t1Rows = t7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t8 : packedMul t2Rows t1Rows = t8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t9 : packedMul bRows t8Rows = t9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

lemma decode_c : decodeRows cRows = matrixA * matrixB := by
  rw [← product_a_b, decode_packedMul]
  rfl

lemma decode_d : decodeRows dRows = matrixA * matrixB * matrixA * matrixB * matrixB := by
  rw [← product_c2_b, decode_packedMul, ← product_c_c, decode_packedMul, decode_c]
  simp only [matrixB, mul_assoc]

lemma decode_t0 : decodeRows t0Rows = ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)) := by
  rw [← product_t0, decode_packedMul, decode_c, decode_d]

lemma decode_t1 : decodeRows t1Rows = (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB))) := by
  rw [← product_t1, decode_packedMul, decode_t0]
  rfl

lemma decode_t2 : decodeRows t2Rows = ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))) := by
  rw [← product_t2, decode_packedMul, decode_c, decode_t1]

lemma decode_t3 : decodeRows t3Rows = ((matrixA * matrixB * matrixA * matrixB * matrixB) * ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB))))) := by
  rw [← product_t3, decode_packedMul, decode_d, decode_t2]

lemma decode_t4 : decodeRows t4Rows = (matrixA * ((matrixA * matrixB * matrixA * matrixB * matrixB) * ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))))) := by
  rw [← product_t4, decode_packedMul, decode_t3]
  rfl

lemma decode_t5 : decodeRows t5Rows = (matrixB * (matrixA * ((matrixA * matrixB * matrixA * matrixB * matrixB) * ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB))))))) := by
  rw [← product_t5, decode_packedMul, decode_t4]
  rfl

lemma decode_t6 : decodeRows t6Rows = ((matrixA * matrixB) * (matrixB * (matrixA * ((matrixA * matrixB * matrixA * matrixB * matrixB) * ((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))))))) := by
  rw [← product_t6, decode_packedMul, decode_c, decode_t5]

lemma decode_t7 : decodeRows t7Rows = ((matrixA * matrixB * matrixA * matrixB * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))) := by
  rw [← product_t7, decode_packedMul, decode_d, decode_t1]

lemma decode_t8 : decodeRows t8Rows = (((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))) := by
  rw [← product_t8, decode_packedMul, decode_t2, decode_t1]

lemma decode_t9 : decodeRows t9Rows = (matrixB * (((matrixA * matrixB) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB)))) * (matrixB * ((matrixA * matrixB) * (matrixA * matrixB * matrixA * matrixB * matrixB))))) := by
  rw [← product_t9, decode_packedMul, decode_t8]
  rfl

end Janko4.Simplicity.WordOrderCertificates
