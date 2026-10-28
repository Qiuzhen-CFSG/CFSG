module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 1). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block7_rows :
    Data.t2Block7.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (224 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block8_rows :
    Data.t2Block8.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (256 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block9_rows :
    Data.t2Block9.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (288 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block10_rows :
    Data.t2Block10.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (320 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block11_rows :
    Data.t2Block11.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (352 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block12_rows :
    Data.t2Block12.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (384 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block13_rows :
    Data.t2Block13.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (416 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
