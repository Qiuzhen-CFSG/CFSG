module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.UInput
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.U.Complete
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Rows

/-!
# Complete U-square product certificate

The complete checked row certificate is combined with the initial widening
bridge to obtain the literal matrix identity `U * U = U2` for the fixed
published candidates.  No generator identification is used.

Source: ATLAS M24G1-P1; see the `source/README.md` files in MixedWords and
CubeProducts.  Every numerical leaf equation is kernel checked.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts

open Inputs

/-- The fixed candidate U matrix squares to the fixed candidate U2 matrix. -/
theorem USquare_product : Data.u * Data.u = Data.u2 := by
  exact u_square_of_rows initial_u_bridge USquare_rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
