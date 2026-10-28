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

theorem product_675 : packedMul r666Rows r670Rows = r671Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_676 : packedMul r663Rows r671Rows = r672Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_677 : packedMul yRows r25Rows = r673Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_678 : packedMul r31Rows r86Rows = r674Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_679 : packedMul r90Rows r674Rows = r675Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_680 : packedMul r673Rows r675Rows = r676Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_681 : packedMul r62Rows r135Rows = r677Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_682 : packedMul r165Rows r677Rows = r678Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_683 : packedMul r173Rows r145Rows = r679Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_684 : packedMul r87Rows r679Rows = r680Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_685 : packedMul r678Rows r680Rows = r681Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_686 : packedMul r676Rows r681Rows = r682Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_687 : packedMul r104Rows r137Rows = r683Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_688 : packedMul r6Rows r24Rows = r684Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_689 : packedMul r58Rows r684Rows = r685Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_690 : packedMul r683Rows r685Rows = r686Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_691 : packedMul r161Rows r184Rows = r687Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_692 : packedMul r4Rows r687Rows = r688Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_693 : packedMul r98Rows r84Rows = r689Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_694 : packedMul r11Rows r689Rows = r690Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_695 : packedMul r688Rows r690Rows = r691Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_696 : packedMul r686Rows r691Rows = r692Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_697 : packedMul r682Rows r692Rows = r693Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_698 : packedMul r138Rows r7Rows = r694Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_699 : packedMul r167Rows r131Rows = r695Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
