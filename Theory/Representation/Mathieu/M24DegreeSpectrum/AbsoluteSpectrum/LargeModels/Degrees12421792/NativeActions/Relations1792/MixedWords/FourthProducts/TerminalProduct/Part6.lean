module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 6). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block42_rows :
    Data.t2Block42.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1344 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block43_rows :
    Data.t2Block43.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1376 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block44_rows :
    Data.t2Block44.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1408 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block45_rows :
    Data.t2Block45.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1440 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block46_rows :
    Data.t2Block46.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1472 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block47_rows :
    Data.t2Block47.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1504 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block48_rows :
    Data.t2Block48.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1536 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
