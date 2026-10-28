module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Products0
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.NaturalCertificate

/-!
# Checked matrix products, batch 1

Five binary products are checked entrywise. The sequential batch imports
keep simultaneous certificate compilation bounded.

Source: the literal ATLAS degree-27 matrices over GF(7) retained in
`CubicExtension/source/`. Generated witnesses are checked by Lean, independently
of the Python generator; see `MatrixWitness/source/README.md`.
-/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness

open MatrixData

-- Each kernel check is memory intensive; check declarations sequentially.
set_option Elab.async false

set_option maxRecDepth 10000 in
theorem product5 : matrix4 * matrixA = matrix5 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product6 : matrix5 * matrixB = matrix6 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product7 : matrixB * matrixA = matrix7 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product8 : matrix7 * matrixB = matrix8 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product9 : inverseB * matrix4 = matrix9 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)


end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
