module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block21 :
    Data.tBlock21.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block21 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block22 :
    Data.tBlock22.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block22 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block23 :
    Data.tBlock23.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block23 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block24 :
    Data.tBlock24.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block24 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block25 :
    Data.tBlock25.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block25 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block26 :
    Data.tBlock26.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block26 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block27 :
    Data.tBlock27.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block27 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
