module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 7). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block49_rows :
    Data.t2Block49.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1568 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block50_rows :
    Data.t2Block50.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1600 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block51_rows :
    Data.t2Block51.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1632 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block52_rows :
    Data.t2Block52.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1664 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block53_rows :
    Data.t2Block53.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1696 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block54_rows :
    Data.t2Block54.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1728 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block55_rows :
    Data.t2Block55.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (1760 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
