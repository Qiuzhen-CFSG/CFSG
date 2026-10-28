module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.WordOrders.Prime31Tables

/-!
# Kernel-checked power products for the J4 word of order 31

Packed rows are witnesses only: the accompanying products are checked by the
Lean kernel and decoded using `decode_packedMul`. The words and bit convention
come from `Model.Simplicity.Words` and `Model.Data`, following
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

public section
namespace Janko4.Simplicity.WordOrderCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_p31e2 : packedMul t7Rows t7Rows = p31e2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p31e3 : packedMul p31e2Rows t7Rows = p31e3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p31e6 : packedMul p31e3Rows p31e3Rows = p31e6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p31e7 : packedMul p31e6Rows t7Rows = p31e7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p31e14 : packedMul p31e7Rows p31e7Rows = p31e14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p31e15 : packedMul p31e14Rows t7Rows = p31e15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p31e30 : packedMul p31e15Rows p31e15Rows = p31e30Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_p31e31 : packedMul p31e30Rows t7Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Janko4.Simplicity.WordOrderCertificates
