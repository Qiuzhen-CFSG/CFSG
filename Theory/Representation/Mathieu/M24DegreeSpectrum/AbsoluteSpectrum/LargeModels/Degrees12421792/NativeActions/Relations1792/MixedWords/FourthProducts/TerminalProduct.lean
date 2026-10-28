module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part0
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part1
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part4
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part5
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part6
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct.Part7

/-!
# The complete terminal T2-square certificate

The eight imported parts check all 1792 dense rows against the identity table.
The list assembly below only reorganizes the immutable 56 blocks; the product
itself is then discharged by the checked fixed-width arithmetic.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Arithmetic

theorem rows :
    Data.t2Rows.map (fun a => row a WideT2.blocks) =
      (List.range 1792).map (fun i => 2^i) := by
  simp only [Data.t2Rows, Data.t2Blocks, List.flatten_cons, List.flatten_nil,
    List.map_append, block0_rows, block1_rows, block2_rows, block3_rows,
    block4_rows, block5_rows, block6_rows, block7_rows, block8_rows,
    block9_rows, block10_rows, block11_rows, block12_rows, block13_rows,
    block14_rows, block15_rows, block16_rows, block17_rows, block18_rows,
    block19_rows, block20_rows, block21_rows, block22_rows, block23_rows,
    block24_rows, block25_rows, block26_rows, block27_rows, block28_rows,
    block29_rows, block30_rows, block31_rows, block32_rows, block33_rows,
    block34_rows, block35_rows, block36_rows, block37_rows, block38_rows,
    block39_rows, block40_rows, block41_rows, block42_rows, block43_rows,
    block44_rows, block45_rows, block46_rows, block47_rows, block48_rows,
    block49_rows, block50_rows, block51_rows, block52_rows, block53_rows,
    block54_rows, block55_rows]
  decide +kernel

theorem t_fourth : Data.t2 * Data.t2 = 1 := by
  have hp := product Data.t2Rows Data.t2Rows
    ((List.range 1792).map (fun i => 2^i)) WideT2.blocks
    Data.t2Rows_length Data.t2Rows_length WideT2.bridge WideT2.blocks_lengths rows
  exact hp.trans (decode_identity 1792)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
