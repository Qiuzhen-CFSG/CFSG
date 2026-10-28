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

theorem product_375 : packedMul r366Rows r370Rows = r371Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_376 : packedMul r17Rows r147Rows = r372Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_377 : packedMul r14Rows r29Rows = r373Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_378 : packedMul r372Rows r373Rows = r374Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_379 : packedMul r14Rows r38Rows = r375Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_380 : packedMul r152Rows r3Rows = r376Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_381 : packedMul r62Rows r376Rows = r377Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_382 : packedMul r375Rows r377Rows = r378Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_383 : packedMul r374Rows r378Rows = r379Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_384 : packedMul r371Rows r379Rows = r380Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_385 : packedMul r63Rows r67Rows = r381Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_386 : packedMul r4Rows r381Rows = r382Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_387 : packedMul r98Rows r143Rows = r383Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_388 : packedMul r161Rows r383Rows = r384Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_389 : packedMul r382Rows r384Rows = r385Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_390 : packedMul r4Rows r122Rows = r386Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_391 : packedMul r14Rows r386Rows = r387Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_392 : packedMul r123Rows r9Rows = r388Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_393 : packedMul r11Rows r388Rows = r389Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_394 : packedMul r387Rows r389Rows = r390Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_395 : packedMul r385Rows r390Rows = r391Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_396 : packedMul r108Rows r162Rows = r392Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_397 : packedMul r118Rows r162Rows = r393Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_398 : packedMul r392Rows r393Rows = r394Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_399 : packedMul r393Rows r271Rows = r395Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
