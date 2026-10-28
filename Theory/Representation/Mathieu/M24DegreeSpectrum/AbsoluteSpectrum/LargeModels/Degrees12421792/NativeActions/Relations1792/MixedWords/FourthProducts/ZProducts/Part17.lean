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
private theorem square_numeric17_0 :
    (Data.zBlock17.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block17.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric17_1 :
    ((Data.zBlock17.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block17.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric17_2 :
    ((Data.zBlock17.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z2Block17.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_numeric17_3 :
    (Data.zBlock17.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z2Block17.drop 24) := by decide +kernel

theorem square_block17 :
    Data.zBlock17.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z2Block17 :=
  RowArithmetic.of_chunks Data.zBlock17 Data.z2Block17 WideZ.blocks
    WideZ.blocks_lengths square_numeric17_0 square_numeric17_1 square_numeric17_2 square_numeric17_3

set_option maxRecDepth 8192 in
private theorem cube_numeric17_0 :
    (Data.z2Block17.take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block17.take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric17_1 :
    ((Data.z2Block17.drop 8).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block17.drop 8).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric17_2 :
    ((Data.z2Block17.drop 16).take 8).map (fun a => RowArithmetic.row a WideZ.blocks) =
      ((Data.z3Block17.drop 16).take 8) := by decide +kernel

set_option maxRecDepth 8192 in
private theorem cube_numeric17_3 :
    (Data.z2Block17.drop 24).map (fun a => RowArithmetic.row a WideZ.blocks) =
      (Data.z3Block17.drop 24) := by decide +kernel

theorem cube_block17 :
    Data.z2Block17.map (fun a => Arithmetic.row a WideZ.blocks) =
      Data.z3Block17 :=
  RowArithmetic.of_chunks Data.z2Block17 Data.z3Block17 WideZ.blocks
    WideZ.blocks_lengths cube_numeric17_0 cube_numeric17_1 cube_numeric17_2 cube_numeric17_3

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts
