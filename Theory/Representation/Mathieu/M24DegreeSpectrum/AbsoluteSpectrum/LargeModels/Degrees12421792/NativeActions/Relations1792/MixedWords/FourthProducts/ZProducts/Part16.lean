module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts.RowArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.WideZ
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthData

/-!
# Exact Z-square and Z-cube row certificates

Each check uses the immutable original row blocks. The proved widening
and arithmetic checker connect these equalities to matrix multiplication.
Source: ATLAS M24G1-P1; see `ZProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts

set_option maxRecDepth 8192 in
private theorem square_numeric16_0 :
    (Data.zBlock16.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block16.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric16_1 :
    ((Data.zBlock16.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block16.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric16_2 :
    ((Data.zBlock16.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block16.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric16_3 :
    (Data.zBlock16.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block16.drop 24) := by decide +kernel

theorem square_block16 :
    Data.zBlock16.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z2Block16 :=
  RowArithmetic.of_chunks Data.zBlock16 Data.z2Block16 WideZ.blocks
    WideZ.blocks_lengths square_numeric16_0 square_numeric16_1 square_numeric16_2 square_numeric16_3

set_option maxRecDepth 8192 in
private theorem cube_numeric16_0 :
    (Data.z2Block16.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block16.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric16_1 :
    ((Data.z2Block16.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block16.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric16_2 :
    ((Data.z2Block16.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block16.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric16_3 :
    (Data.z2Block16.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block16.drop 24) := by decide +kernel

theorem cube_block16 :
    Data.z2Block16.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z3Block16 :=
  RowArithmetic.of_chunks Data.z2Block16 Data.z3Block16 WideZ.blocks
    WideZ.blocks_lengths cube_numeric16_0 cube_numeric16_1 cube_numeric16_2 cube_numeric16_3

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts
