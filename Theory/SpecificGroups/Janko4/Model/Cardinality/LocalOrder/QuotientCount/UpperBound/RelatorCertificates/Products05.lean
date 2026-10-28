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

theorem product_125 : packedMul r71Rows r8Rows = r123Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_126 : packedMul r8Rows r61Rows = r124Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_127 : packedMul r2Rows r5Rows = r125Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_128 : packedMul r19Rows r3Rows = r126Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_129 : packedMul r72Rows r86Rows = r127Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_130 : packedMul r127Rows r101Rows = r128Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_131 : packedMul r128Rows r100Rows = r129Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_132 : packedMul r12Rows r79Rows = r130Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_133 : packedMul r11Rows r94Rows = r131Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_134 : packedMul r103Rows r114Rows = r132Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_135 : packedMul r59Rows r119Rows = r133Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_136 : packedMul r2Rows r21Rows = r134Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_137 : packedMul r60Rows r113Rows = r135Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_138 : packedMul r11Rows r12Rows = r136Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_139 : packedMul r91Rows r61Rows = r137Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_140 : packedMul r0Rows r4Rows = r138Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_141 : packedMul r0Rows r7Rows = r139Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_142 : packedMul r18Rows r83Rows = r140Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_143 : packedMul r105Rows r58Rows = r141Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_144 : packedMul r123Rows r1Rows = r142Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_145 : packedMul r71Rows r106Rows = r143Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_146 : packedMul r0Rows r46Rows = r144Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_147 : packedMul r24Rows r89Rows = r145Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_148 : packedMul r55Rows r2Rows = r146Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_149 : packedMul r146Rows r20Rows = r147Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
