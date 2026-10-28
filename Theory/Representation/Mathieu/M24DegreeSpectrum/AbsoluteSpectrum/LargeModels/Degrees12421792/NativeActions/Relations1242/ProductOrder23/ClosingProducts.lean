module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Thirteenth
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23.ClosingProducts.Identity

/-!
# The two final literal products in the degree-1242 order-23 chain

The closing products are checked directly on the literal packed matrices.  No
semantic power or native-action premise enters either equality. Each family
checks all 1242 rows, then `CF.product` translates the certificates to ordinary
matrix multiplication. The identity output uses `decode_identityRows`.

Source: ATLAS M24G1-P1, word 2, and the original untransposed matrices
M24G1-f2r1242B0.m1/.m2. See `ClosingProducts/source/README.md`.
These equalities discharge h13 and h23 of `product_order23_of_products` and
`product_word2_of_products`; the earlier products stay with their producers.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
open Tables

/-- The checked thirteenth-power addition-chain product. -/
theorem closing_thirteenth : Tables.c10 * Tables.c3 = Tables.c13 :=
  ClosingProducts.Thirteenth.product

/-- The checked final product is the literal identity matrix. -/
theorem closing_identity : Tables.c13 * Tables.c10 = 1 :=
  ClosingProducts.Identity.product

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
