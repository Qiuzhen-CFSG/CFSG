module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.USquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.UCube
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.VSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.VCube
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.Inverse
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.Circuit

/-!
# Five literal cube products for the fifth ATLAS word

The fixed matrices satisfy U²=U2, U2 U=U3, V²=V2, V2 V=V3,
and U3 V3=1. The source application retains precisely the four
independently produced prefix equations.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords

/-- Source clause 5 with all five cube-product premises discharged.
The independent prefix producer supplies the four remaining equations. -/
theorem fifth_word_of_prefix_products
    (hy : Data.x * Data1242.second = Data.y)
    (hz : Data.x * Data.y = Data.z)
    (hu : Data.x * Data.z = Data.u)
    (hv : Data.z * Data.y = Data.v) :
    Presentation.rowRelatorValues Data1242.first Data1242.second 5 = 1 :=
  fifth_word_of_products hy hz hu hv u_square u_cube v_square v_cube cube_inverse

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
