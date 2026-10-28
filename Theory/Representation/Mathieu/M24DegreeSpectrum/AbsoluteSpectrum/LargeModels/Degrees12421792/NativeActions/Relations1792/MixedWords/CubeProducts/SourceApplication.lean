module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.Circuit

/-!
# The checked cubes applied to the literal mixed source word

All five cube-product premises of the source circuit are discharged here.
The five shared-prefix products remain with the independent prefix producer
and the final mixed-word assembly owner. Source: ATLAS M24G1-P1, clause 5;
see `../source/README.md`. No generator convention is changed.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords

/-- Only the independent shared-prefix certificates remain. -/
theorem fifth_word_of_prefix_products
    (hx : Data1792.first * Data1792.second = Data.x)
    (hy : Data.x * Data1792.second = Data.y)
    (hz : Data.x * Data.y = Data.z)
    (hu : Data.x * Data.z = Data.u)
    (hv : Data.z * Data.y = Data.v) :
    Presentation.rowRelatorValues Data1792.first Data1792.second 5 = 1 := by
  exact fifth_word_of_products hx hy hz hu hv u_square u_cube v_square v_cube cubes_inverse

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords
