module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Products4

/-!
# Checked matrix products, batch 5

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
theorem product25 : matrix24 * matrix14 = matrix25 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product26 : matrix12 * matrix12 = matrix26 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product27 : matrix26 * matrix12 = matrix27 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product28 : matrix25 * matrix27 = 1 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product29 : matrix14 * matrix4 = matrix29 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)


end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
