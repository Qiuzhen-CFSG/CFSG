module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Batch0
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Batch1
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Batch2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Batch3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Batch4
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Batch5
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.USquare.Batch6

/-!
# The complete U-square numerical row certificate

The 56 checked blocks cover all 1,792 rows of the fixed candidate U matrix.
Concatenation preserves the exact accumulation and compression expression
required by `u_square_of_rows`; the complete input bridge is supplied separately.

Source: ATLAS M24G1-P1. See `source/README.md` and the source notes in
MixedWords and CubeProducts. Every numerical leaf equation is kernel checked.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
open Arithmetic Inputs

/-- All rows of the literal U-square product equal the published U2 rows. -/
theorem USquare_rows :
    Data.uRows.map (fun a => compressBlocks 32 56 (accumChunks a uWide)) =
      Data.u2Rows := by
  exact map_flatten (fun a => compressBlocks 32 56 (accumChunks a uWide))
    (.cons USquare_rows_0
    (.cons USquare_rows_1
    (.cons USquare_rows_2
    (.cons USquare_rows_3
    (.cons USquare_rows_4
    (.cons USquare_rows_5
    (.cons USquare_rows_6
    (.cons USquare_rows_7
    (.cons USquare_rows_8
    (.cons USquare_rows_9
    (.cons USquare_rows_10
    (.cons USquare_rows_11
    (.cons USquare_rows_12
    (.cons USquare_rows_13
    (.cons USquare_rows_14
    (.cons USquare_rows_15
    (.cons USquare_rows_16
    (.cons USquare_rows_17
    (.cons USquare_rows_18
    (.cons USquare_rows_19
    (.cons USquare_rows_20
    (.cons USquare_rows_21
    (.cons USquare_rows_22
    (.cons USquare_rows_23
    (.cons USquare_rows_24
    (.cons USquare_rows_25
    (.cons USquare_rows_26
    (.cons USquare_rows_27
    (.cons USquare_rows_28
    (.cons USquare_rows_29
    (.cons USquare_rows_30
    (.cons USquare_rows_31
    (.cons USquare_rows_32
    (.cons USquare_rows_33
    (.cons USquare_rows_34
    (.cons USquare_rows_35
    (.cons USquare_rows_36
    (.cons USquare_rows_37
    (.cons USquare_rows_38
    (.cons USquare_rows_39
    (.cons USquare_rows_40
    (.cons USquare_rows_41
    (.cons USquare_rows_42
    (.cons USquare_rows_43
    (.cons USquare_rows_44
    (.cons USquare_rows_45
    (.cons USquare_rows_46
    (.cons USquare_rows_47
    (.cons USquare_rows_48
    (.cons USquare_rows_49
    (.cons USquare_rows_50
    (.cons USquare_rows_51
    (.cons USquare_rows_52
    (.cons USquare_rows_53
    (.cons USquare_rows_54
    (.cons USquare_rows_55
    .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
