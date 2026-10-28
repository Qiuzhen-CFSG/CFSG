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

theorem product_650 : packedMul r62Rows r5Rows = r646Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_651 : packedMul r172Rows r628Rows = r647Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_652 : packedMul r646Rows r647Rows = r648Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_653 : packedMul r645Rows r648Rows = r649Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_654 : packedMul r78Rows r99Rows = r650Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_655 : packedMul r87Rows r96Rows = r651Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_656 : packedMul r111Rows r651Rows = r652Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_657 : packedMul r650Rows r652Rows = r653Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_658 : packedMul r21Rows r170Rows = r654Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_659 : packedMul r654Rows r640Rows = r655Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_660 : packedMul r653Rows r655Rows = r656Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_661 : packedMul r649Rows r656Rows = r657Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_662 : packedMul r46Rows r83Rows = r658Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_663 : packedMul r62Rows r39Rows = r659Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_664 : packedMul r658Rows r659Rows = r660Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_665 : packedMul r87Rows r173Rows = r661Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_666 : packedMul r552Rows r661Rows = r662Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_667 : packedMul r660Rows r662Rows = r663Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_668 : packedMul r16Rows r40Rows = r664Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_669 : packedMul r184Rows r15Rows = r665Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_670 : packedMul r664Rows r665Rows = r666Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_671 : packedMul r129Rows r6Rows = r667Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_672 : packedMul r184Rows r126Rows = r668Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_673 : packedMul r104Rows r668Rows = r669Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_674 : packedMul r667Rows r669Rows = r670Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
