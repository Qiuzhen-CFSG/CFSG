module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts.ZSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts.ZCube
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts.TProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts.TSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.FourthProducts.T2Square
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.Circuit

/-!
# The five fixed products for the nested fourth ATLAS word

On the published untransposed matrices we certify Z², Z³, XZ³, T² and
(T²)² = 1. All numerical rows and all widened-table comparisons are checked
by the kernel. The final application discharges these five premises of
`sixth_word_of_products`; it retains exactly the two shared prefix equations.
Their independent producer and the final source-word assembly remain with
the prefix and mixed-word owners. No matrix-product premise is needed for
the five numerical equations themselves.

Source: John Bray's ATLAS M24G1-P1, positive clause 6 (zero-based), on
M24G1-f2r1242B0.m1/.m2. See `FourthProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords

theorem z_square : Data.z * Data.z = Data.z2 := FourthProducts.zSquare

theorem z_cube : Data.z2 * Data.z = Data.z3 := FourthProducts.zCube

theorem t_product : Data.x * Data.z3 = Data.t := FourthProducts.tProduct

theorem t_square : Data.t * Data.t = Data.t2 := FourthProducts.tSquare

theorem t2_square : Data.t2 * Data.t2 = 1 := FourthProducts.t2Square

/-- Literal source clause 6 with all five fourth-branch products discharged.
Only the independent shared-prefix certificates remain explicit. -/
theorem sixth_word_of_prefix_products
    (hy : Data.x * Data1242.second = Data.y)
    (hz : Data.x * Data.y = Data.z) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 6 = 1 :=
  sixth_word_of_products hy hz z_square z_cube t_product t_square t2_square

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
