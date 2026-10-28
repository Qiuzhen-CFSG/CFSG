module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.U
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeData

/-!
# The checked U input blocks applied to the two literal products

All but the first eight widened input blocks are checked for the actual
published U matrix. Those initial blocks and the output-row checks remain. These
are precisely the U-square and U-cube premises of the mixed-word circuit;
they do not identify U with any word in the original generators.

Source: ATLAS M24G1-P1; see `source/README.md` and `../source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
open Arithmetic Inputs

/-- Apply the checked later input blocks to the U-square product. -/
theorem u_square_of_rows (hi : InitialUBridge)
    (h : Data.uRows.map (fun a => compressBlocks 32 56 (accumChunks a uWide)) =
      Data.u2Rows) : Data.u * Data.u = Data.u2 := by
  exact product_chunks 32 56 (by decide) Data.uRows Data.uRows Data.u2Rows uWide
    Data.uRows_length Data.uRows_length (u_wide_of_initial_blocks hi) h

/-- The same input bridge applies to the distinct U2 left factor. -/
theorem u_cube_of_rows (hi : InitialUBridge)
    (h : Data.u2Rows.map (fun a => compressBlocks 32 56 (accumChunks a uWide)) =
      Data.u3Rows) : Data.u2 * Data.u = Data.u3 := by
  exact product_chunks 32 56 (by decide) Data.u2Rows Data.uRows Data.u3Rows uWide
    Data.u2Rows_length Data.uRows_length (u_wide_of_initial_blocks hi) h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
