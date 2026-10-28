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

theorem product_250 : packedMul r6Rows r246Rows = r247Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_251 : packedMul r28Rows xRows = r248Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_252 : packedMul r71Rows r248Rows = r249Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_253 : packedMul r247Rows r249Rows = r250Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_254 : packedMul r245Rows r250Rows = r251Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_255 : packedMul r0Rows r38Rows = r252Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_256 : packedMul r16Rows r97Rows = r253Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_257 : packedMul r121Rows r253Rows = r254Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_258 : packedMul r252Rows r254Rows = r255Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_259 : packedMul r15Rows r8Rows = r256Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_260 : packedMul r90Rows xRows = r257Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_261 : packedMul r147Rows r257Rows = r258Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_262 : packedMul r256Rows r258Rows = r259Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_263 : packedMul r255Rows r259Rows = r260Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_264 : packedMul r124Rows r7Rows = r261Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_265 : packedMul r108Rows r261Rows = r262Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_266 : packedMul r5Rows r148Rows = r263Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_267 : packedMul r125Rows r77Rows = r264Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_268 : packedMul r263Rows r264Rows = r265Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_269 : packedMul r262Rows r265Rows = r266Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_270 : packedMul r44Rows r60Rows = r267Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_271 : packedMul r62Rows r19Rows = r268Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_272 : packedMul r267Rows r268Rows = r269Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_273 : packedMul r1Rows r5Rows = r270Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_274 : packedMul r30Rows r15Rows = r271Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
