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

theorem product_500 : packedMul r9Rows r495Rows = r496Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_501 : packedMul r494Rows r496Rows = r497Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_502 : packedMul r73Rows r469Rows = r498Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_503 : packedMul r60Rows r62Rows = r499Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_504 : packedMul r16Rows r499Rows = r500Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_505 : packedMul r498Rows r500Rows = r501Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_506 : packedMul r497Rows r501Rows = r502Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_507 : packedMul r131Rows r106Rows = r503Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_508 : packedMul r90Rows r312Rows = r504Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_509 : packedMul r503Rows r504Rows = r505Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_510 : packedMul r145Rows r6Rows = r506Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_511 : packedMul r10Rows r506Rows = r507Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_512 : packedMul r32Rows xRows = r508Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_513 : packedMul r12Rows r508Rows = r509Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_514 : packedMul r507Rows r509Rows = r510Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_515 : packedMul r505Rows r510Rows = r511Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_516 : packedMul r502Rows r511Rows = r512Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_517 : packedMul r0Rows r64Rows = r513Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_518 : packedMul r167Rows r87Rows = r514Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_519 : packedMul r513Rows r514Rows = r515Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_520 : packedMul r49Rows r20Rows = r516Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_521 : packedMul r170Rows r173Rows = r517Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_522 : packedMul r516Rows r517Rows = r518Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_523 : packedMul r515Rows r518Rows = r519Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_524 : packedMul r7Rows r9Rows = r520Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
