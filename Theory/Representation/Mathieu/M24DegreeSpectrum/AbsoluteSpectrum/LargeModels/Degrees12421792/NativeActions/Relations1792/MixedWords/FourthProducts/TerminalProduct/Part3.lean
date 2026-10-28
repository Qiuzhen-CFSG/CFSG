module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 3). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block21_rows :
    Data.t2Block21.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (672 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block22_rows :
    Data.t2Block22.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (704 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block23_rows :
    Data.t2Block23.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (736 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block24_rows :
    Data.t2Block24.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (768 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block25_rows :
    Data.t2Block25.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (800 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block26_rows :
    Data.t2Block26.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (832 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block27_rows :
    Data.t2Block27.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (864 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
