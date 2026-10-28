module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.Witnesses

/-!
# MaskProducts for the local kernel

These witnesses implement the ATLAS `J4G1-max1W1` words documented in
`Cardinality.Subgroup` and the conjugates in `KernelCount.BinarySpan`.
Packed products are checked by Lean's kernel; `decode_packedMul` transfers
these certificates to binary matrices. No external computation is trusted.
-/

public section
namespace Janko4.Cardinality.KernelCount.Relations
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem product_m224_6 : packedMul e6Rows e7Rows = m224_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m224_5 : packedMul e5Rows m224_6Rows = m224_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1952_9 : packedMul e9Rows e10Rows = m1952_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1952_8 : packedMul e8Rows m1952_9Rows = m1952_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1952_7 : packedMul e7Rows m1952_8Rows = m1952_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1952_5 : packedMul e5Rows m1952_7Rows = m1952_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1991_9 : packedMul e9Rows e10Rows = m1991_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1991_8 : packedMul e8Rows m1991_9Rows = m1991_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1991_7 : packedMul e7Rows m1991_8Rows = m1991_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1991_6 : packedMul e6Rows m1991_7Rows = m1991_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1991_2 : packedMul e2Rows m1991_6Rows = m1991_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1991_1 : packedMul e1Rows m1991_2Rows = m1991_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1991_0 : packedMul e0Rows m1991_1Rows = m1991_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.KernelCount.Relations
