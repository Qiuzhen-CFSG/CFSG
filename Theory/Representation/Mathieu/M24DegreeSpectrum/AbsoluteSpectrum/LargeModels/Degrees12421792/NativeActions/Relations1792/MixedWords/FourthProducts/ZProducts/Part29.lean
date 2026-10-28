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
private theorem square_numeric29_0 :
    (Data.zBlock29.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block29.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric29_1 :
    ((Data.zBlock29.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block29.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric29_2 :
    ((Data.zBlock29.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block29.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric29_3 :
    (Data.zBlock29.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block29.drop 24) := by decide +kernel

theorem square_block29 :
    Data.zBlock29.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z2Block29 :=
  RowArithmetic.of_chunks Data.zBlock29 Data.z2Block29 WideZ.blocks
    WideZ.blocks_lengths square_numeric29_0 square_numeric29_1 square_numeric29_2 square_numeric29_3

set_option maxRecDepth 8192 in
private theorem cube_numeric29_0 :
    (Data.z2Block29.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block29.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric29_1 :
    ((Data.z2Block29.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block29.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric29_2 :
    ((Data.z2Block29.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block29.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric29_3 :
    (Data.z2Block29.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block29.drop 24) := by decide +kernel

theorem cube_block29 :
    Data.z2Block29.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z3Block29 :=
  RowArithmetic.of_chunks Data.z2Block29 Data.z3Block29 WideZ.blocks
    WideZ.blocks_lengths cube_numeric29_0 cube_numeric29_1 cube_numeric29_2 cube_numeric29_3

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts
