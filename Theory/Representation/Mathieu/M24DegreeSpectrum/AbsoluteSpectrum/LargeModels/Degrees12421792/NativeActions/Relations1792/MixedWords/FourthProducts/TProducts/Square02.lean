module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block14 :
    Data.tBlock14.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block14 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block15 :
    Data.tBlock15.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block15 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block16 :
    Data.tBlock16.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block16 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block17 :
    Data.tBlock17.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block17 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block18 :
    Data.tBlock18.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block18 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block19 :
    Data.tBlock19.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block19 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block20 :
    Data.tBlock20.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block20 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
