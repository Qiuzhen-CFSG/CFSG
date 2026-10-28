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

theorem product_475 : packedMul r468Rows r470Rows = r471Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_476 : packedMul r4Rows r7Rows = r472Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_477 : packedMul r6Rows xRows = r473Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_478 : packedMul r70Rows r473Rows = r474Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_479 : packedMul r472Rows r474Rows = r475Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_480 : packedMul r471Rows r475Rows = r476Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_481 : packedMul r467Rows r476Rows = r477Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_482 : packedMul r6Rows r10Rows = r478Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_483 : packedMul r211Rows r478Rows = r479Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_484 : packedMul r81Rows r9Rows = r480Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_485 : packedMul r129Rows r24Rows = r481Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_486 : packedMul r11Rows r481Rows = r482Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_487 : packedMul r480Rows r482Rows = r483Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_488 : packedMul r479Rows r483Rows = r484Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_489 : packedMul r170Rows r96Rows = r485Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_490 : packedMul r73Rows r17Rows = r486Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_491 : packedMul r485Rows r486Rows = r487Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_492 : packedMul r112Rows r5Rows = r488Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_493 : packedMul r136Rows r9Rows = r489Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_494 : packedMul r50Rows r489Rows = r490Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_495 : packedMul r488Rows r490Rows = r491Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_496 : packedMul r487Rows r491Rows = r492Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_497 : packedMul r484Rows r492Rows = r493Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_498 : packedMul r138Rows r155Rows = r494Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_499 : packedMul r125Rows r172Rows = r495Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
