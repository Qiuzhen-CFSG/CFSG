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

theorem product_100 : packedMul r3Rows r9Rows = r98Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_101 : packedMul r28Rows r32Rows = r99Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_102 : packedMul r11Rows r85Rows = r100Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_103 : packedMul r4Rows r1Rows = r101Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_104 : packedMul r21Rows r45Rows = r102Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_105 : packedMul r88Rows r32Rows = r103Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_106 : packedMul r20Rows r40Rows = r104Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_107 : packedMul r14Rows r61Rows = r105Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_108 : packedMul r11Rows r15Rows = r106Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_109 : packedMul r11Rows r84Rows = r107Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_110 : packedMul r1Rows r6Rows = r108Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_111 : packedMul r68Rows r25Rows = r109Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_112 : packedMul r37Rows r10Rows = r110Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_113 : packedMul r78Rows r62Rows = r111Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_114 : packedMul r45Rows r58Rows = r112Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_115 : packedMul r28Rows r79Rows = r113Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_116 : packedMul r15Rows r76Rows = r114Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_117 : packedMul r2Rows r3Rows = r115Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_118 : packedMul r115Rows r76Rows = r116Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_119 : packedMul r30Rows r10Rows = r117Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_120 : packedMul r117Rows r6Rows = r118Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_121 : packedMul r80Rows r77Rows = r119Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_122 : packedMul r11Rows xRows = r120Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_123 : packedMul r10Rows r89Rows = r121Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_124 : packedMul r82Rows r47Rows = r122Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
