module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block42 :
    Data.tBlock42.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block42 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block43 :
    Data.tBlock43.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block43 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block44 :
    Data.tBlock44.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block44 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block45 :
    Data.tBlock45.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block45 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block46 :
    Data.tBlock46.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block46 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block47 :
    Data.tBlock47.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block47 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block48 :
    Data.tBlock48.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block48 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
