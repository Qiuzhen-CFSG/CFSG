module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.RepresentativeRows

/-!
# Certified packed products for the J4 order-three word

Each declaration checks 112 natural-number XOR equalities by kernel reduction.
The numeric witnesses alone are not trusted; `decode_packedMul` gives their
ordinary binary-matrix interpretation.
-/

public section
namespace Janko4.Simplicity.ThreesCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_prefix2Rows : packedMul aRows bRows = prefix2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix3Rows : packedMul prefix2Rows bRows = prefix3Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix4Rows : packedMul prefix3Rows aRows = prefix4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix5Rows : packedMul prefix4Rows bRows = prefix5Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix6Rows : packedMul prefix5Rows aRows = prefix6Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix7Rows : packedMul prefix6Rows bRows = prefix7Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix8Rows : packedMul prefix7Rows aRows = prefix8Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix9Rows : packedMul prefix8Rows bRows = prefix9Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_prefix10Rows : packedMul prefix9Rows bRows = prefix10Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_power2Rows : packedMul prefix10Rows prefix10Rows = power2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_power4Rows : packedMul power2Rows power2Rows = power4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_power8Rows : packedMul power4Rows power4Rows = power8Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_power16Rows : packedMul power8Rows power8Rows = power16Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_power20Rows : packedMul power16Rows power4Rows = power20Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_power22Rows : packedMul power20Rows power2Rows = power22Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_power44Rows : packedMul power22Rows power22Rows = power44Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_packedOne : packedMul power44Rows power22Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Janko4.Simplicity.ThreesCertificates
