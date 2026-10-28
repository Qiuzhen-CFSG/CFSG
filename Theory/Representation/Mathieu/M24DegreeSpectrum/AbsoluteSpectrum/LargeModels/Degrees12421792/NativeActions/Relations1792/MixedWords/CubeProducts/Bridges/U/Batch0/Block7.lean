module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Inputs.U
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.Checker

/-!
# Initial U widening block 7

The balanced conversion skips zero tails and is proved equal to the original
base-2048 expansion. Every literal equation is kernel checked.
Source: ATLAS M24G1-P1; see CubeProducts/source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
open Arithmetic Inputs

set_option maxRecDepth 8192 in
private theorem checked : uWideBlock7 =
    Data.uBlock7.map (GeneratorOrders.expandTree 6 1792) := by
  decide +kernel

theorem u_wide_7 :
    uWideBlock7 = Data.uBlock7.map (expandBlocks 32 56) := by
  have he : GeneratorOrders.expandTree 6 1792 = expandBlocks 32 56 := by
    funext a
    rw [GeneratorOrders.expandTree_eq, expandBlocks_eq]
  simpa only [he] using checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
