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
private theorem square_numeric20_0 :
    (Data.zBlock20.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block20.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric20_1 :
    ((Data.zBlock20.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block20.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric20_2 :
    ((Data.zBlock20.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block20.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric20_3 :
    (Data.zBlock20.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block20.drop 24) := by decide +kernel

theorem square_block20 :
    Data.zBlock20.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z2Block20 :=
  RowArithmetic.of_chunks Data.zBlock20 Data.z2Block20 WideZ.blocks
    WideZ.blocks_lengths square_numeric20_0 square_numeric20_1 square_numeric20_2 square_numeric20_3

set_option maxRecDepth 8192 in
private theorem cube_numeric20_0 :
    (Data.z2Block20.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block20.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric20_1 :
    ((Data.z2Block20.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block20.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric20_2 :
    ((Data.z2Block20.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block20.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric20_3 :
    (Data.z2Block20.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block20.drop 24) := by decide +kernel

theorem cube_block20 :
    Data.z2Block20.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z3Block20 :=
  RowArithmetic.of_chunks Data.z2Block20 Data.z3Block20 WideZ.blocks
    WideZ.blocks_lengths cube_numeric20_0 cube_numeric20_1 cube_numeric20_2 cube_numeric20_3

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts
