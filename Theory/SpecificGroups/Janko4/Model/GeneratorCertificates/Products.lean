module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Tables

/-!
# Kernel-checked packed products for the J4 generators

Each certificate checks 112 row equalities using natural-number XOR.
The soundness theorem in `Packed` transfers them to GF(2) matrices.
The witnesses in `Tables` are untrusted input to these kernel reductions.
-/

public section
namespace Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_a_a : packedMul aRows aRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_b_b : packedMul bRows bRows = b2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_b2_b2 : packedMul b2Rows b2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_a_b : packedMul aRows bRows = cRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c_c : packedMul cRows cRows = c2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c2_c2 : packedMul c2Rows c2Rows = c4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c4_c4 : packedMul c4Rows c4Rows = c8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c8_c8 : packedMul c8Rows c8Rows = c16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c16_c16 : packedMul c16Rows c16Rows = c32Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c32_c4 : packedMul c32Rows c4Rows = c36Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c36_c : packedMul c36Rows cRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_c2_b : packedMul c2Rows bRows = dRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_d_d : packedMul dRows dRows = d2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_d2_d2 : packedMul d2Rows d2Rows = d4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_d4_d : packedMul d4Rows dRows = d5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_d5_d5 : packedMul d5Rows d5Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Janko4.GeneratorCertificates
