module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 2). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block14_rows :
    Data.t2Block14.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (448 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block15_rows :
    Data.t2Block15.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (480 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block16_rows :
    Data.t2Block16.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (512 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block17_rows :
    Data.t2Block17.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (544 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block18_rows :
    Data.t2Block18.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (576 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block19_rows :
    Data.t2Block19.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (608 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block20_rows :
    Data.t2Block20.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (640 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
