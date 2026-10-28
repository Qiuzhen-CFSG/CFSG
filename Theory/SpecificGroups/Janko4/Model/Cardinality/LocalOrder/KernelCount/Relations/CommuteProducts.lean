module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.Witnesses

/-!
# CommuteProducts for the local kernel

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

theorem product_square0 : packedMul e0Rows e0Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_comm0_1 : packedMul e0Rows e1Rows = comm0_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_0 : packedMul e1Rows e0Rows = comm0_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_2 : packedMul e0Rows e2Rows = comm0_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_0 : packedMul e2Rows e0Rows = comm0_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_3 : packedMul e0Rows e3Rows = comm0_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_0 : packedMul e3Rows e0Rows = comm0_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_4 : packedMul e0Rows e4Rows = comm0_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_0 : packedMul e4Rows e0Rows = comm0_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_5 : packedMul e0Rows e5Rows = comm0_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_0 : packedMul e5Rows e0Rows = comm0_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_6 : packedMul e0Rows e6Rows = comm0_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_0 : packedMul e6Rows e0Rows = comm0_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_7 : packedMul e0Rows e7Rows = comm0_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_0 : packedMul e7Rows e0Rows = comm0_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_8 : packedMul e0Rows e8Rows = comm0_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_0 : packedMul e8Rows e0Rows = comm0_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_9 : packedMul e0Rows e9Rows = comm0_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_0 : packedMul e9Rows e0Rows = comm0_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm0_10 : packedMul e0Rows e10Rows = comm0_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_0 : packedMul e10Rows e0Rows = comm0_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_2 : packedMul e1Rows e2Rows = comm1_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_1 : packedMul e2Rows e1Rows = comm1_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_3 : packedMul e1Rows e3Rows = comm1_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_1 : packedMul e3Rows e1Rows = comm1_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_4 : packedMul e1Rows e4Rows = comm1_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_1 : packedMul e4Rows e1Rows = comm1_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_5 : packedMul e1Rows e5Rows = comm1_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_1 : packedMul e5Rows e1Rows = comm1_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_6 : packedMul e1Rows e6Rows = comm1_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_1 : packedMul e6Rows e1Rows = comm1_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_7 : packedMul e1Rows e7Rows = comm1_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_1 : packedMul e7Rows e1Rows = comm1_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_8 : packedMul e1Rows e8Rows = comm1_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_1 : packedMul e8Rows e1Rows = comm1_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_9 : packedMul e1Rows e9Rows = comm1_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_1 : packedMul e9Rows e1Rows = comm1_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_10 : packedMul e1Rows e10Rows = comm1_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_1 : packedMul e10Rows e1Rows = comm1_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_3 : packedMul e2Rows e3Rows = comm2_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_2 : packedMul e3Rows e2Rows = comm2_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_4 : packedMul e2Rows e4Rows = comm2_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_2 : packedMul e4Rows e2Rows = comm2_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_5 : packedMul e2Rows e5Rows = comm2_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_2 : packedMul e5Rows e2Rows = comm2_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_6 : packedMul e2Rows e6Rows = comm2_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_2 : packedMul e6Rows e2Rows = comm2_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_7 : packedMul e2Rows e7Rows = comm2_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_2 : packedMul e7Rows e2Rows = comm2_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_8 : packedMul e2Rows e8Rows = comm2_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_2 : packedMul e8Rows e2Rows = comm2_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_9 : packedMul e2Rows e9Rows = comm2_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_2 : packedMul e9Rows e2Rows = comm2_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_10 : packedMul e2Rows e10Rows = comm2_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_2 : packedMul e10Rows e2Rows = comm2_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_4 : packedMul e3Rows e4Rows = comm3_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_3 : packedMul e4Rows e3Rows = comm3_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_5 : packedMul e3Rows e5Rows = comm3_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_3 : packedMul e5Rows e3Rows = comm3_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_6 : packedMul e3Rows e6Rows = comm3_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_3 : packedMul e6Rows e3Rows = comm3_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_7 : packedMul e3Rows e7Rows = comm3_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_3 : packedMul e7Rows e3Rows = comm3_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_8 : packedMul e3Rows e8Rows = comm3_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_3 : packedMul e8Rows e3Rows = comm3_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_9 : packedMul e3Rows e9Rows = comm3_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_3 : packedMul e9Rows e3Rows = comm3_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_10 : packedMul e3Rows e10Rows = comm3_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_3 : packedMul e10Rows e3Rows = comm3_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_5 : packedMul e4Rows e5Rows = comm4_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_4 : packedMul e5Rows e4Rows = comm4_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_6 : packedMul e4Rows e6Rows = comm4_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_4 : packedMul e6Rows e4Rows = comm4_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_7 : packedMul e4Rows e7Rows = comm4_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_4 : packedMul e7Rows e4Rows = comm4_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_8 : packedMul e4Rows e8Rows = comm4_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_4 : packedMul e8Rows e4Rows = comm4_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_9 : packedMul e4Rows e9Rows = comm4_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_4 : packedMul e9Rows e4Rows = comm4_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_10 : packedMul e4Rows e10Rows = comm4_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_4 : packedMul e10Rows e4Rows = comm4_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_6 : packedMul e5Rows e6Rows = comm5_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_5 : packedMul e6Rows e5Rows = comm5_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_7 : packedMul e5Rows e7Rows = comm5_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_5 : packedMul e7Rows e5Rows = comm5_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_8 : packedMul e5Rows e8Rows = comm5_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_5 : packedMul e8Rows e5Rows = comm5_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_9 : packedMul e5Rows e9Rows = comm5_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_5 : packedMul e9Rows e5Rows = comm5_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_10 : packedMul e5Rows e10Rows = comm5_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_5 : packedMul e10Rows e5Rows = comm5_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_7 : packedMul e6Rows e7Rows = comm6_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_6 : packedMul e7Rows e6Rows = comm6_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_8 : packedMul e6Rows e8Rows = comm6_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_6 : packedMul e8Rows e6Rows = comm6_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_9 : packedMul e6Rows e9Rows = comm6_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_6 : packedMul e9Rows e6Rows = comm6_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_10 : packedMul e6Rows e10Rows = comm6_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_6 : packedMul e10Rows e6Rows = comm6_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_8 : packedMul e7Rows e8Rows = comm7_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_7 : packedMul e8Rows e7Rows = comm7_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_9 : packedMul e7Rows e9Rows = comm7_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_7 : packedMul e9Rows e7Rows = comm7_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_10 : packedMul e7Rows e10Rows = comm7_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_7 : packedMul e10Rows e7Rows = comm7_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_9 : packedMul e8Rows e9Rows = comm8_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_8 : packedMul e9Rows e8Rows = comm8_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_10 : packedMul e8Rows e10Rows = comm8_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_8 : packedMul e10Rows e8Rows = comm8_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_10 : packedMul e9Rows e10Rows = comm9_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_9 : packedMul e10Rows e9Rows = comm9_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.KernelCount.Relations
