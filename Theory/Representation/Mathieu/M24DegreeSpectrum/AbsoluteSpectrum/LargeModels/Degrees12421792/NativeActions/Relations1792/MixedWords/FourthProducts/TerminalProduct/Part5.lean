module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 5). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block35_rows :
    Data.t2Block35.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1120 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block36_rows :
    Data.t2Block36.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1152 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block37_rows :
    Data.t2Block37.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1184 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block38_rows :
    Data.t2Block38.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1216 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block39_rows :
    Data.t2Block39.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1248 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block40_rows :
    Data.t2Block40.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1280 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block41_rows :
    Data.t2Block41.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1312 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
