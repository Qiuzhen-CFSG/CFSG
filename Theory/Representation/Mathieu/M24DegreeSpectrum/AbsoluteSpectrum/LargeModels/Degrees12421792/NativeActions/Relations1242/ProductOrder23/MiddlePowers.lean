module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Fifth
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.MiddlePowers.Tenth

/-!
# Two literal middle products in the degree-1242 addition chain

The row certificates prove c2 * c3 = c5 and c5 * c5 = c10 without
assuming any earlier power identity. They discharge h5 and h10 of
`Relations1242.product_order23_of_products` and `product_word2_of_products`.
The parent assembly retains the earlier and closing product obligations.

Source: ATLAS M24G1-P1, word 2, and the original untransposed matrices
M24G1-f2r1242B0.m1/.m2. See MiddlePowers/source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23

/-- The literal table product supplying the fifth-power step. -/
theorem middle_fifth : Tables.c2 * Tables.c3 = Tables.c5 :=
  MiddlePowers.Fifth.product

/-- The literal table product supplying the tenth-power step. -/
theorem middle_tenth : Tables.c5 * Tables.c5 = Tables.c10 :=
  MiddlePowers.Tenth.product

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
