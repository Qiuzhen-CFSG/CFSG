module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT

/-! Complete numerical row blocks for the literal T·T = T2 certificate.

Kernel checks retain the published rows and their order. The matrix
application is in `TProducts.lean`; see `TProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts

set_option maxRecDepth 8192 in
theorem square_block35 :
    Data.tBlock35.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block35 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block36 :
    Data.tBlock36.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block36 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block37 :
    Data.tBlock37.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block37 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block38 :
    Data.tBlock38.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block38 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block39 :
    Data.tBlock39.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block39 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block40 :
    Data.tBlock40.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block40 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square_block41 :
    Data.tBlock41.map (fun a => Arithmetic.row a WideT.blocks) =
      Data.t2Block41 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
