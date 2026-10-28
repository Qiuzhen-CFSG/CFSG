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

theorem product_25 : packedMul r12Rows r8Rows = r23Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_26 : packedMul r2Rows r10Rows = r24Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_27 : packedMul r5Rows r1Rows = r25Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_28 : packedMul r9Rows r5Rows = r26Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_29 : packedMul r8Rows r17Rows = r27Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_30 : packedMul r8Rows r4Rows = r28Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_31 : packedMul r5Rows r2Rows = r29Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_32 : packedMul r27Rows r22Rows = r30Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_33 : packedMul r6Rows r2Rows = r31Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_34 : packedMul r1Rows r9Rows = r32Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_35 : packedMul r7Rows r4Rows = r33Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_36 : packedMul r20Rows r23Rows = r34Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_37 : packedMul r12Rows r16Rows = r35Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_38 : packedMul r33Rows r25Rows = r36Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_39 : packedMul r30Rows r9Rows = r37Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_40 : packedMul r6Rows r6Rows = r38Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_41 : packedMul r19Rows r21Rows = r39Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_42 : packedMul r18Rows r13Rows = r40Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_43 : packedMul r13Rows r1Rows = r41Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_44 : packedMul r31Rows r39Rows = r42Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_45 : packedMul r42Rows r36Rows = r43Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_46 : packedMul r7Rows r7Rows = r44Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_47 : packedMul r1Rows r14Rows = r45Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_48 : packedMul r4Rows r18Rows = r46Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_49 : packedMul r37Rows r2Rows = r47Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
