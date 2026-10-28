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

theorem product_150 : packedMul r65Rows r1Rows = r148Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_151 : packedMul r109Rows r109Rows = r149Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_152 : packedMul r110Rows r65Rows = r150Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_153 : packedMul r2Rows r50Rows = r151Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_154 : packedMul r126Rows r11Rows = r152Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_155 : packedMul r98Rows xRows = r153Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_156 : packedMul r11Rows r21Rows = r154Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_157 : packedMul r14Rows r15Rows = r155Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_158 : packedMul r7Rows r90Rows = r156Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_159 : packedMul r7Rows r93Rows = r157Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_160 : packedMul r87Rows r8Rows = r158Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_161 : packedMul r24Rows r112Rows = r159Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_162 : packedMul r10Rows r50Rows = r160Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_163 : packedMul r24Rows r40Rows = r161Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_164 : packedMul r124Rows r116Rows = r162Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_165 : packedMul r133Rows r2Rows = r163Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_166 : packedMul r163Rows r68Rows = r164Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_167 : packedMul r18Rows r34Rows = r165Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_168 : packedMul r12Rows r40Rows = r166Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_169 : packedMul r10Rows r130Rows = r167Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_170 : packedMul r32Rows r3Rows = r168Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_171 : packedMul r168Rows r26Rows = r169Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_172 : packedMul r169Rows r69Rows = r170Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_173 : packedMul r27Rows r134Rows = r171Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_174 : packedMul r171Rows r7Rows = r172Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
