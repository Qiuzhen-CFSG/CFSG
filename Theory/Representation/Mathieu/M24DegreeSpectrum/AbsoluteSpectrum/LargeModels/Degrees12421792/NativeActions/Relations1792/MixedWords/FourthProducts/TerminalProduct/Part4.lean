module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 4). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block28_rows :
    Data.t2Block28.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (896 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block29_rows :
    Data.t2Block29.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (928 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block30_rows :
    Data.t2Block30.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (960 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block31_rows :
    Data.t2Block31.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (992 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block32_rows :
    Data.t2Block32.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1024 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block33_rows :
    Data.t2Block33.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1056 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block34_rows :
    Data.t2Block34.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1088 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
