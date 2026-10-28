module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.UInput
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.VSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.VCube
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.Inverse

/-!
# The five fixed mixed-word cube products

Each equality is a complete binary matrix product, certified on all 1792 rows.
The independently checked widening bridges connect every base-2048 input to
the published candidate data; carry-free arithmetic then proves the products.
In particular the two distinct cube matrices multiply to the identity.

These are the five cube premises of `mixed_cubes_of_products` in `Circuit`.
Connecting the fixed U and V matrices to the source generators belongs to the
shared-prefix certificates. See `CubeProducts/SourceApplication.lean` for the
literal source consumer, and `CubeProducts/source/README.md` for measurements.
Source: John Bray's ATLAS M24G1-P1, clause 5, in the original row convention.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords

theorem u_square : Data.u * Data.u = Data.u2 := CubeProducts.USquare_product

theorem u_cube : Data.u2 * Data.u = Data.u3 := CubeProducts.UCube_product

theorem v_square : Data.v * Data.v = Data.v2 := CubeProducts.VSquare_product

theorem v_cube : Data.v2 * Data.v = Data.v3 := CubeProducts.VCube_product

theorem cubes_inverse : Data.u3 * Data.v3 = 1 := CubeProducts.Inverse_product

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords
