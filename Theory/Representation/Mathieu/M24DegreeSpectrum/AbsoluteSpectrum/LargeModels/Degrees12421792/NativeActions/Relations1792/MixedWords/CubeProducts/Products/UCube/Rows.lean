module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Batch0
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Batch1
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Batch2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Batch3
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Batch4
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Batch5
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.UCube.Batch6

/-!
# Complete numerical U-cube rows

Multiply every fixed U2 row by the fixed widened U table and obtain the
fixed U3 rows. The 56 block certificates cover rows 0 through 1791;
`map_flatten` assembles them without omitting any row. This is the numerical
premise consumed by `u_cube_of_rows`.

Source: ATLAS M24G1-P1; see the `source/README.md` files in MixedWords,
CubeProducts, and Products/USquare.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
open Arithmetic

open Inputs

theorem UCube_rows :
    Data.u2Rows.map (fun a => compressBlocks 32 56 (accumChunks a uWide)) =
      Data.u3Rows := by
  exact map_flatten (fun a => compressBlocks 32 56 (accumChunks a uWide))
    (.cons UCube_rows_0
    (.cons UCube_rows_1
    (.cons UCube_rows_2
    (.cons UCube_rows_3
    (.cons UCube_rows_4
    (.cons UCube_rows_5
    (.cons UCube_rows_6
    (.cons UCube_rows_7
    (.cons UCube_rows_8
    (.cons UCube_rows_9
    (.cons UCube_rows_10
    (.cons UCube_rows_11
    (.cons UCube_rows_12
    (.cons UCube_rows_13
    (.cons UCube_rows_14
    (.cons UCube_rows_15
    (.cons UCube_rows_16
    (.cons UCube_rows_17
    (.cons UCube_rows_18
    (.cons UCube_rows_19
    (.cons UCube_rows_20
    (.cons UCube_rows_21
    (.cons UCube_rows_22
    (.cons UCube_rows_23
    (.cons UCube_rows_24
    (.cons UCube_rows_25
    (.cons UCube_rows_26
    (.cons UCube_rows_27
    (.cons UCube_rows_28
    (.cons UCube_rows_29
    (.cons UCube_rows_30
    (.cons UCube_rows_31
    (.cons UCube_rows_32
    (.cons UCube_rows_33
    (.cons UCube_rows_34
    (.cons UCube_rows_35
    (.cons UCube_rows_36
    (.cons UCube_rows_37
    (.cons UCube_rows_38
    (.cons UCube_rows_39
    (.cons UCube_rows_40
    (.cons UCube_rows_41
    (.cons UCube_rows_42
    (.cons UCube_rows_43
    (.cons UCube_rows_44
    (.cons UCube_rows_45
    (.cons UCube_rows_46
    (.cons UCube_rows_47
    (.cons UCube_rows_48
    (.cons UCube_rows_49
    (.cons UCube_rows_50
    (.cons UCube_rows_51
    (.cons UCube_rows_52
    (.cons UCube_rows_53
    (.cons UCube_rows_54
    (.cons UCube_rows_55
    .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts
