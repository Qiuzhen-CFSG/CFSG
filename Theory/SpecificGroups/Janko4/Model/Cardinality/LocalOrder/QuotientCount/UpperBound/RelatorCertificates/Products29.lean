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

theorem product_725 : packedMul r74Rows r92Rows = r721Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_726 : packedMul r157Rows r721Rows = r722Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_727 : packedMul r720Rows r722Rows = r723Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_728 : packedMul r718Rows r723Rows = r724Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_729 : packedMul r19Rows r567Rows = r725Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_730 : packedMul r141Rows r5Rows = r726Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_731 : packedMul r25Rows r726Rows = r727Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_732 : packedMul r725Rows r727Rows = r728Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_733 : packedMul r136Rows r39Rows = r729Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_734 : packedMul r50Rows r729Rows = r730Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_735 : packedMul r165Rows r300Rows = r731Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_736 : packedMul r730Rows r731Rows = r732Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_737 : packedMul r728Rows r732Rows = r733Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_738 : packedMul r724Rows r733Rows = r734Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_739 : packedMul e8Rows e10Rows = r735Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_740 : packedMul e6Rows r735Rows = r736Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_741 : packedMul e2Rows r736Rows = r194Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_742 : packedMul e8Rows e9Rows = r737Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_743 : packedMul e7Rows r737Rows = r738Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_744 : packedMul e6Rows r738Rows = r739Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_745 : packedMul e5Rows r739Rows = r740Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_746 : packedMul e4Rows r740Rows = r741Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_747 : packedMul e3Rows r741Rows = r742Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_748 : packedMul e1Rows r742Rows = r201Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_749 : packedMul e4Rows r736Rows = r743Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
