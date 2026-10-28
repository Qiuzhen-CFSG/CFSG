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

theorem product_550 : packedMul r543Rows r545Rows = r546Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_551 : packedMul r542Rows r546Rows = r547Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_552 : packedMul r538Rows r547Rows = r548Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_553 : packedMul yRows r156Rows = r549Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_554 : packedMul r93Rows r10Rows = r550Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_555 : packedMul r549Rows r550Rows = r551Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_556 : packedMul r7Rows r135Rows = r552Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_557 : packedMul r19Rows r1Rows = r553Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_558 : packedMul r552Rows r553Rows = r554Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_559 : packedMul r551Rows r554Rows = r555Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_560 : packedMul r82Rows r183Rows = r556Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_561 : packedMul r159Rows r10Rows = r557Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_562 : packedMul r556Rows r557Rows = r558Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_563 : packedMul r4Rows r132Rows = r559Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_564 : packedMul r47Rows r84Rows = r560Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_565 : packedMul r559Rows r560Rows = r561Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_566 : packedMul r558Rows r561Rows = r562Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_567 : packedMul r555Rows r562Rows = r563Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_568 : packedMul r0Rows r109Rows = r564Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_569 : packedMul r68Rows r85Rows = r565Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_570 : packedMul r564Rows r565Rows = r566Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_571 : packedMul r77Rows r1Rows = r567Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_572 : packedMul r557Rows r567Rows = r568Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_573 : packedMul r566Rows r568Rows = r569Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_574 : packedMul r2Rows r8Rows = r570Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
