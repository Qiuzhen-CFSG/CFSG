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

theorem product_175 : packedMul r96Rows r10Rows = r173Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_176 : packedMul r10Rows r102Rows = r174Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_177 : packedMul r174Rows r1Rows = r175Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_178 : packedMul r175Rows r24Rows = r176Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_179 : packedMul r176Rows r43Rows = r177Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_180 : packedMul r177Rows r28Rows = r178Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_181 : packedMul r178Rows r4Rows = r179Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_182 : packedMul r179Rows r102Rows = r180Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_183 : packedMul r118Rows r28Rows = r181Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_184 : packedMul r181Rows r18Rows = r182Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_185 : packedMul r182Rows r35Rows = r183Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_186 : packedMul r17Rows r92Rows = r184Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_187 : packedMul r44Rows r44Rows = r185Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_188 : packedMul yRows r185Rows = r186Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_189 : packedMul r18Rows xRows = r187Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_190 : packedMul r7Rows r187Rows = r188Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_191 : packedMul r186Rows r188Rows = e1Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_192 : packedMul r12Rows r88Rows = r189Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_193 : packedMul r0Rows r189Rows = r190Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_194 : packedMul r88Rows r103Rows = r191Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_195 : packedMul r2Rows xRows = r192Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_196 : packedMul r191Rows r192Rows = r193Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_197 : packedMul r190Rows r193Rows = r194Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_198 : packedMul r0Rows r1Rows = r195Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_199 : packedMul r64Rows r11Rows = r196Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
