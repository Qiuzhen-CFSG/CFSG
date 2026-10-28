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

theorem product_600 : packedMul r86Rows r595Rows = r596Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_601 : packedMul r594Rows r596Rows = r597Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_602 : packedMul r25Rows r14Rows = r598Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_603 : packedMul r78Rows r598Rows = r599Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_604 : packedMul r15Rows xRows = r600Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_605 : packedMul r10Rows r600Rows = r601Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_606 : packedMul r599Rows r601Rows = r602Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_607 : packedMul r597Rows r602Rows = r603Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_608 : packedMul r593Rows r603Rows = r604Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_609 : packedMul r1Rows r68Rows = r605Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_610 : packedMul r86Rows r45Rows = r606Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_611 : packedMul r5Rows r606Rows = r607Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_612 : packedMul r605Rows r607Rows = r608Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_613 : packedMul r4Rows r82Rows = r609Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_614 : packedMul r6Rows r104Rows = r610Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_615 : packedMul r183Rows r610Rows = r611Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_616 : packedMul r609Rows r611Rows = r612Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_617 : packedMul r608Rows r612Rows = r613Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_618 : packedMul r17Rows r47Rows = r614Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_619 : packedMul r95Rows r34Rows = r615Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_620 : packedMul r94Rows r615Rows = r616Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_621 : packedMul r614Rows r616Rows = r617Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_622 : packedMul r96Rows r20Rows = r618Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_623 : packedMul r29Rows r3Rows = r619Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_624 : packedMul r8Rows r619Rows = r620Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
