module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.UInput
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.U.Complete
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Rows

/-!
# Complete U-cube product certificate

The complete checked row certificate is combined with the initial widening
bridge to obtain the literal matrix identity `U2 * U = U3` for the fixed
published candidates.  No generator identification is used.

Source: ATLAS M24G1-P1; see the `source/README.md` files in MixedWords and
CubeProducts.  Every numerical leaf equation is kernel checked.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts

open Inputs

/-- The fixed candidate U2 matrix times U equals the fixed candidate U3 matrix. -/
theorem UCube_product : Data.u2 * Data.u = Data.u3 := by
  exact u_cube_of_rows initial_u_bridge UCube_rows

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
