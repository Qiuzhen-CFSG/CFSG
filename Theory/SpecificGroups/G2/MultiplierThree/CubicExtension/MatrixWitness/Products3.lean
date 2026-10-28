module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Products2

/-!
# Checked matrix products, batch 3

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
theorem product15 : matrix14 * matrix14 = matrix15 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product16 : matrix15 * matrix15 = matrix16 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product17 : matrix16 * matrix3 = 1 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product18 : matrix6 * matrix6 = matrix18 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product19 : matrix18 * matrix6 = matrix19 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)


end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
