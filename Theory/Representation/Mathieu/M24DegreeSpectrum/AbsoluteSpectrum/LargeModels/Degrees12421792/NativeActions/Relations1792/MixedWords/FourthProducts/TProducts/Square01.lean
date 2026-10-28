module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block7 :
    Data.tBlock7.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block7 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block8 :
    Data.tBlock8.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block8 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block9 :
    Data.tBlock9.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block9 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block10 :
    Data.tBlock10.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block10 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block11 :
    Data.tBlock11.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block11 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block12 :
    Data.tBlock12.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block12 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block13 :
    Data.tBlock13.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block13 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
