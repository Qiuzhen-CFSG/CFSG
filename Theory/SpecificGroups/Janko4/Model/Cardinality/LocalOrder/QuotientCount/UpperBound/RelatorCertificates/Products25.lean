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

theorem product_625 : packedMul r618Rows r620Rows = r621Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_626 : packedMul r617Rows r621Rows = r622Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_627 : packedMul r613Rows r622Rows = r623Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_628 : packedMul r3Rows r154Rows = r624Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_629 : packedMul r132Rows r172Rows = r625Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_630 : packedMul r4Rows r625Rows = r626Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_631 : packedMul r624Rows r626Rows = r627Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_632 : packedMul r10Rows r32Rows = r628Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_633 : packedMul r158Rows r8Rows = r629Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_634 : packedMul r111Rows r629Rows = r630Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_635 : packedMul r628Rows r630Rows = r631Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_636 : packedMul r627Rows r631Rows = r632Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_637 : packedMul r66Rows r136Rows = r633Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_638 : packedMul r56Rows r166Rows = r634Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_639 : packedMul r7Rows r634Rows = r635Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_640 : packedMul r633Rows r635Rows = r636Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_641 : packedMul r101Rows r87Rows = r637Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_642 : packedMul r80Rows r637Rows = r638Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_643 : packedMul r137Rows r4Rows = r639Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_644 : packedMul r49Rows r639Rows = r640Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_645 : packedMul r638Rows r640Rows = r641Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_646 : packedMul r636Rows r641Rows = r642Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_647 : packedMul r632Rows r642Rows = r643Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_648 : packedMul r73Rows r2Rows = r644Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_649 : packedMul r644Rows r540Rows = r645Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
