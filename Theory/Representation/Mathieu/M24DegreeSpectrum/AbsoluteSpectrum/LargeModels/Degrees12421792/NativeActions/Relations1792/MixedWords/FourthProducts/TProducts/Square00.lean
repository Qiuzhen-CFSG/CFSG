module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block0 :
    Data.tBlock0.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block0 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block1 :
    Data.tBlock1.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block1 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block2 :
    Data.tBlock2.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block2 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block3 :
    Data.tBlock3.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block3 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block4 :
    Data.tBlock4.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block4 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block5 :
    Data.tBlock5.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block5 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block6 :
    Data.tBlock6.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block6 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
