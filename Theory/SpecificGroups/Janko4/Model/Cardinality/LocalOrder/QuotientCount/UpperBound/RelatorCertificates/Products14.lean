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

theorem product_350 : packedMul r343Rows r345Rows = r346Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_351 : packedMul r29Rows r14Rows = r347Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_352 : packedMul r14Rows r347Rows = r348Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_353 : packedMul r38Rows r113Rows = r349Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_354 : packedMul r131Rows r107Rows = r350Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_355 : packedMul r349Rows r350Rows = r351Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_356 : packedMul r348Rows r351Rows = r352Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_357 : packedMul r346Rows r352Rows = r353Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_358 : packedMul r80Rows r132Rows = r354Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_359 : packedMul yRows r354Rows = r355Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_360 : packedMul r111Rows r8Rows = r356Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_361 : packedMul r92Rows r356Rows = r357Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_362 : packedMul r355Rows r357Rows = r358Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_363 : packedMul r59Rows r160Rows = r359Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_364 : packedMul r44Rows r359Rows = r360Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_365 : packedMul r100Rows r192Rows = r361Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_366 : packedMul r360Rows r361Rows = r362Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_367 : packedMul r358Rows r362Rows = r363Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_368 : packedMul r41Rows r34Rows = r364Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_369 : packedMul r96Rows r8Rows = r365Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_370 : packedMul r364Rows r365Rows = r366Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_371 : packedMul r35Rows r24Rows = r367Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_372 : packedMul r15Rows r11Rows = r368Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_373 : packedMul r45Rows r368Rows = r369Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_374 : packedMul r367Rows r369Rows = r370Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
