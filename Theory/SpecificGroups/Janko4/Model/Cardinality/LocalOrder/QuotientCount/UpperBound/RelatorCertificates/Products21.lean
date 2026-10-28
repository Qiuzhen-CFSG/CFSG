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

theorem product_525 : packedMul r82Rows r92Rows = r521Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_526 : packedMul r520Rows r521Rows = r522Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_527 : packedMul r15Rows r129Rows = r523Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_528 : packedMul r31Rows r153Rows = r524Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_529 : packedMul r523Rows r524Rows = r525Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_530 : packedMul r522Rows r525Rows = r526Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_531 : packedMul r519Rows r526Rows = r527Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_532 : packedMul r180Rows r180Rows = r528Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_533 : packedMul r180Rows r528Rows = r529Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_534 : packedMul r0Rows r97Rows = r530Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_535 : packedMul r1Rows r41Rows = r531Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_536 : packedMul r119Rows r531Rows = r532Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_537 : packedMul r530Rows r532Rows = r533Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_538 : packedMul r83Rows r41Rows = r534Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_539 : packedMul r6Rows r8Rows = r535Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_540 : packedMul r70Rows r535Rows = r536Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_541 : packedMul r534Rows r536Rows = r537Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_542 : packedMul r533Rows r537Rows = r538Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_543 : packedMul r65Rows r151Rows = r539Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_544 : packedMul r67Rows r43Rows = r540Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_545 : packedMul r152Rows r540Rows = r541Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_546 : packedMul r539Rows r541Rows = r542Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_547 : packedMul r8Rows r10Rows = r543Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_548 : packedMul r32Rows r107Rows = r544Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_549 : packedMul r21Rows r544Rows = r545Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.Cardinality.QuotientCount.UpperBound.RelatorCertificates
