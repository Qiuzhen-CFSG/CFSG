module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeLower.Square
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TablePowers.ThreeLower.Cube

/-!
# The square and cube of the fixed degree-1792 commutator table

`ThreeLower.square` and `ThreeLower.cube` certify the complete literal products
`three * three = threeSquare` and `threeSquare * three = threeCube` over `ZMod 2`.
Every row is checked in one of 56 blocks. The shared widened-table certificate
identifies every base-2048 row with the expansion of its original binary row;
`GeneratorOrders.product_fast` then translates the checked parity computations
into ordinary matrix multiplication.

These are the first two product premises of
`CommutatorWords.wordThree_pow_twelve_of_products`. The later powers and the
comparison of `three` with the original positive generator word are separate
certificate obligations. Source: ATLAS M24G1-P1, positive word 3; see `source/README.md`
and `../source/README.md` for the literal tables and word conventions.
-/
