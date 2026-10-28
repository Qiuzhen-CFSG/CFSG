module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.U.Batch0

/-!
# Complete widening of the fixed U matrix

The balanced conversion skips zero tails and is proved equal to the original
base-2048 expansion. Every literal equation is kernel checked.
Source: ATLAS M24G1-P1; see CubeProducts/source/README.md.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
open Arithmetic Inputs

/-- Every widened row equals expansion of the corresponding published U row. -/
theorem u_wide : uWide.flatten = Data.uRows.map (expandBlocks 32 56) :=
  u_wide_of_initial_blocks initial_u_bridge

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
