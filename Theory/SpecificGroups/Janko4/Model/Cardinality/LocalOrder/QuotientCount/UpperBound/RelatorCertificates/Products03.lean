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

theorem product_75 : packedMul r10Rows r1Rows = r73Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_76 : packedMul r31Rows r13Rows = r74Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_77 : packedMul r7Rows r35Rows = r75Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_78 : packedMul r26Rows r74Rows = r76Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_79 : packedMul r66Rows r67Rows = r77Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_80 : packedMul r10Rows r60Rows = r78Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_81 : packedMul r57Rows r50Rows = r79Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_82 : packedMul r4Rows r4Rows = r80Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_83 : packedMul r36Rows r29Rows = r81Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_84 : packedMul r64Rows r17Rows = r82Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_85 : packedMul r70Rows r2Rows = r83Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_86 : packedMul r3Rows xRows = r84Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_87 : packedMul r13Rows r75Rows = r85Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_88 : packedMul r3Rows r17Rows = r86Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_89 : packedMul r22Rows r69Rows = r87Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_90 : packedMul r57Rows r12Rows = r88Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_91 : packedMul r81Rows r19Rows = r89Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_92 : packedMul r14Rows r58Rows = r90Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_93 : packedMul r20Rows r45Rows = r91Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_94 : packedMul r37Rows r6Rows = r92Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_95 : packedMul r6Rows r5Rows = r93Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_96 : packedMul r20Rows r43Rows = r94Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_97 : packedMul r11Rows r73Rows = r95Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_98 : packedMul r28Rows r72Rows = r96Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_99 : packedMul r18Rows r59Rows = r97Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
