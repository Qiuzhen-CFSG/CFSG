module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Rows
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.FastArithmetic

/-!
# Shared-subword certificates for the local presentation

The words and masks are from `UpperBound.Data` and its adjacent
`source/relator_masks.json`. The generator matrices implement the ATLAS
`J4G1-max1W1` program. Repeated subwords are factored into binary products;
all proposed products are checked by kernel reduction of packed arithmetic.
The external generator supplies witnesses only, never trusted evaluations.
-/

public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
open KernelCount KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem product_0 : packedMul yRows yRows = r0Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_1 : packedMul xRows xRows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

theorem product_2 : packedMul yRows r0Rows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

theorem product_3 : packedMul xRows yRows = r1Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_4 : packedMul xRows r0Rows = r2Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_5 : packedMul r2Rows r1Rows = r3Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_6 : packedMul r3Rows r1Rows = r4Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_7 : packedMul r2Rows r4Rows = r5Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_8 : packedMul r2Rows r2Rows = r6Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_9 : packedMul r1Rows r1Rows = r7Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_10 : packedMul r3Rows r5Rows = r8Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_11 : packedMul r3Rows r6Rows = r9Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_12 : packedMul r3Rows r4Rows = r10Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_13 : packedMul r3Rows r2Rows = r11Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_14 : packedMul r5Rows r4Rows = r12Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_15 : packedMul r5Rows r7Rows = r13Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_16 : packedMul r9Rows r8Rows = r14Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_17 : packedMul r3Rows r3Rows = r15Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_18 : packedMul r1Rows r4Rows = r16Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_19 : packedMul r11Rows r8Rows = r17Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_20 : packedMul r7Rows r1Rows = r18Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_21 : packedMul r11Rows r5Rows = r19Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_22 : packedMul r3Rows r10Rows = r20Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_23 : packedMul r3Rows r8Rows = r21Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_24 : packedMul r2Rows r15Rows = r22Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
