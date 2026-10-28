module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideT2

/-! Dense numerical certificates for terminal T2-square rows (part 0). -/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

set_option maxRecDepth 8192 in
theorem block0_rows :
    Data.t2Block0.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (0 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block1_rows :
    Data.t2Block1.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (32 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block2_rows :
    Data.t2Block2.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (64 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block3_rows :
    Data.t2Block3.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (96 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block4_rows :
    Data.t2Block4.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (128 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block5_rows :
    Data.t2Block5.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (160 + i)) := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem block6_rows :
    Data.t2Block6.map (fun a => row a WideT2.blocks) =
      (List.range 32).map (fun i => 2 ^ (192 + i)) := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
