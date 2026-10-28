module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime29Tables

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

set_option maxRecDepth 10000 in
theorem product_p29e2 : packedMul t6Rows t6Rows = p29e2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p29e3 : packedMul p29e2Rows t6Rows = p29e3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p29e6 : packedMul p29e3Rows p29e3Rows = p29e6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p29e7 : packedMul p29e6Rows t6Rows = p29e7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p29e14 : packedMul p29e7Rows p29e7Rows = p29e14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p29e28 : packedMul p29e14Rows p29e14Rows = p29e28Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p29e29 : packedMul p29e28Rows t6Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Janko4.Simplicity.WordOrderCertificates
