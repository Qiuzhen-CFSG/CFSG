module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Products3

/-!
# Checked matrix products, batch 4

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
theorem product20 : matrix19 * matrix19 = matrix20 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product21 : matrix20 * matrix20 = matrix21 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product22 : matrix21 * matrix6 = 1 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product23 : matrix18 * matrix18 = matrix23 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product24 : matrix13 * matrix23 = matrix24 :=
  mul_of_nat_entries _ _ _ (by decide +kernel)


end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
