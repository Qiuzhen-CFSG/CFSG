module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Data

/-!
# Checked matrix products, batch 0

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
theorem product0 : matrixA * matrixA = 1 :=
  mul_of_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product1 : matrixB * matrixB = inverseB :=
  mul_of_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product2 : inverseB * matrixB = 1 :=
  mul_of_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product3 : matrixA * matrixB = matrix3 :=
  mul_of_entries _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product4 : matrixA * inverseB = matrix4 :=
  mul_of_entries _ _ _ (by decide +kernel)


end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
