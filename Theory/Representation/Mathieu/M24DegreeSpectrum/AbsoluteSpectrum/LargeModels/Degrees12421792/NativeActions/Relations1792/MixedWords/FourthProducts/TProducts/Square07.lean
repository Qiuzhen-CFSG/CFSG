module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block49 :
    Data.tBlock49.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block49 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block50 :
    Data.tBlock50.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block50 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block51 :
    Data.tBlock51.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block51 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block52 :
    Data.tBlock52.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block52 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block53 :
    Data.tBlock53.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block53 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block54 :
    Data.tBlock54.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block54 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block55 :
    Data.tBlock55.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block55 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
