module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.Circuit
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts

/-!
# Mixed degree-1792 source words: certificate assembly

The fixed intermediate rows, product certificates, and exact assembly are
public. See `MixedWords/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792

/-- The product of cubes in the fifth positive ATLAS source word. -/
theorem mixed_cubes :
    (Data1792.first * Data1792.second * Data1792.first * Data1792.second *
        Data1792.first * Data1792.second ^ 2) ^ 3 *
      (Data1792.first * Data1792.second * Data1792.first * Data1792.second ^ 2 *
        Data1792.first * Data1792.second ^ 2) ^ 3 = 1 := by
  exact MixedWords.mixed_cubes_of_products
    MixedWords.prefix_x MixedWords.prefix_y MixedWords.prefix_z
    MixedWords.prefix_u MixedWords.prefix_v MixedWords.u_square MixedWords.u_cube
    MixedWords.v_square MixedWords.v_cube MixedWords.cubes_inverse

/-- The nested fourth power in the sixth positive ATLAS source word. -/
theorem nested_fourth :
    (Data1792.first * Data1792.second *
      (Data1792.first * Data1792.second * Data1792.first * Data1792.second ^ 2) ^ 3) ^ 4 = 1 := by
  exact MixedWords.nested_fourth_of_products
    MixedWords.prefix_x MixedWords.prefix_y MixedWords.prefix_z MixedWords.z_square
    MixedWords.z_cube MixedWords.t_product MixedWords.t_square MixedWords.t_fourth

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
