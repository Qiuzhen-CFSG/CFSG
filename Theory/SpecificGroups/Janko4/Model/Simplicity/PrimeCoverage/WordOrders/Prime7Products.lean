module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime7Tables

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

set_option maxRecDepth 10000 in
theorem product_p7e2 : packedMul t9Rows t9Rows = p7e2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e3 : packedMul p7e2Rows t9Rows = p7e3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e6 : packedMul p7e3Rows p7e3Rows = p7e6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e4 : packedMul p7e2Rows p7e2Rows = p7e4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e5 : packedMul p7e4Rows t9Rows = p7e5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e10 : packedMul p7e5Rows p7e5Rows = p7e10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e20 : packedMul p7e10Rows p7e10Rows = p7e20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e21 : packedMul p7e20Rows t9Rows = p7e21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p7e42 : packedMul p7e21Rows p7e21Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Janko4.Simplicity.WordOrderCertificates
