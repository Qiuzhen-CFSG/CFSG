module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Products1

/-!
# Checked matrix products, batch 2

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
theorem product10 : matrixA * matrix9 = matrix10 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product11 : matrix10 * matrixA = matrix11 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product12 : matrix11 * matrix8 = matrix12 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product13 : matrix3 * matrix3 = matrix13 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product14 : matrix13 * matrix3 = matrix14 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)


end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
