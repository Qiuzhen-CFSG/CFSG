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

theorem product_300 : packedMul r154Rows r17Rows = r296Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_301 : packedMul r22Rows r203Rows = r297Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_302 : packedMul r296Rows r297Rows = r298Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_303 : packedMul r111Rows r26Rows = r299Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_304 : packedMul r9Rows xRows = r300Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_305 : packedMul r155Rows r300Rows = r301Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_306 : packedMul r299Rows r301Rows = r302Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_307 : packedMul r298Rows r302Rows = r303Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_308 : packedMul r295Rows r303Rows = r304Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_309 : packedMul yRows r33Rows = r305Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_310 : packedMul r156Rows r93Rows = r306Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_311 : packedMul r305Rows r306Rows = r307Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_312 : packedMul r15Rows r99Rows = r308Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_313 : packedMul r111Rows r100Rows = r309Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_314 : packedMul r308Rows r309Rows = r310Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_315 : packedMul r307Rows r310Rows = r311Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_316 : packedMul r157Rows r38Rows = r312Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_317 : packedMul r3Rows r14Rows = r313Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_318 : packedMul r312Rows r313Rows = r314Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_319 : packedMul r148Rows r2Rows = r315Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_320 : packedMul r11Rows r120Rows = r316Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_321 : packedMul r315Rows r316Rows = r317Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_322 : packedMul r314Rows r317Rows = r318Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_323 : packedMul r311Rows r318Rows = r319Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_324 : packedMul r4Rows r148Rows = r320Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
