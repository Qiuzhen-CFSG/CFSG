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

theorem product_400 : packedMul r394Rows r395Rows = r396Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_401 : packedMul r83Rows r99Rows = r397Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_402 : packedMul r144Rows r397Rows = r398Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_403 : packedMul r99Rows r114Rows = r399Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_404 : packedMul r78Rows r399Rows = r400Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_405 : packedMul r398Rows r400Rows = r401Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_406 : packedMul r33Rows r9Rows = r402Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_407 : packedMul r150Rows r402Rows = r403Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_408 : packedMul r64Rows r9Rows = r404Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_409 : packedMul r3Rows r107Rows = r405Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_410 : packedMul r404Rows r405Rows = r406Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_411 : packedMul r403Rows r406Rows = r407Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_412 : packedMul r401Rows r407Rows = r408Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_413 : packedMul r164Rows r85Rows = r409Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_414 : packedMul r144Rows r409Rows = r410Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_415 : packedMul r15Rows r28Rows = r411Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_416 : packedMul r93Rows r411Rows = r412Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_417 : packedMul r410Rows r412Rows = r413Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_418 : packedMul r47Rows r5Rows = r414Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_419 : packedMul r132Rows r414Rows = r415Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_420 : packedMul r2Rows r84Rows = r416Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_421 : packedMul r73Rows r416Rows = r417Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_422 : packedMul r415Rows r417Rows = r418Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_423 : packedMul r413Rows r418Rows = r419Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_424 : packedMul r139Rows r105Rows = r420Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
