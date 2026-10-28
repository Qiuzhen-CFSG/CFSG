module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block28 :
    Data.tBlock28.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block28 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block29 :
    Data.tBlock29.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block29 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block30 :
    Data.tBlock30.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block30 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block31 :
    Data.tBlock31.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block31 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block32 :
    Data.tBlock32.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block32 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block33 :
    Data.tBlock33.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block33 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block34 :
    Data.tBlock34.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block34 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
