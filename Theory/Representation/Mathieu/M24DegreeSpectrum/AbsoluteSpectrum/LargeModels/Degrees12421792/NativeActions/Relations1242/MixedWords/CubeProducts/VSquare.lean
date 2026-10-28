module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.VSquareChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV

/-!
# The literal product V * V

The complete numerical certificate and checked radix bridge discharge
the hypotheses of ordinary binary matrix multiplication.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords

open CubeProducts
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

private theorem v_square_check :
    checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.vRows Data.v2Rows = true := by
  have h := (checkMap_append _ _ _ _ _ VSquare.check00 (checkMap_append _ _ _ _ _ VSquare.check01 (checkMap_append _ _ _ _ _ VSquare.check02 (checkMap_append _ _ _ _ _ VSquare.check03 (checkMap_append _ _ _ _ _ VSquare.check04 (checkMap_append _ _ _ _ _ VSquare.check05 (checkMap_append _ _ _ _ _ VSquare.check06 (checkMap_append _ _ _ _ _ VSquare.check07 (checkMap_append _ _ _ _ _ VSquare.check08 (checkMap_append _ _ _ _ _ VSquare.check09 (checkMap_append _ _ _ _ _ VSquare.check10 (checkMap_append _ _ _ _ _ VSquare.check11 (checkMap_append _ _ _ _ _ VSquare.check12 (checkMap_append _ _ _ _ _ VSquare.check13 (checkMap_append _ _ _ _ _ VSquare.check14 (checkMap_append _ _ _ _ _ VSquare.check15 (checkMap_append _ _ _ _ _ VSquare.check16 (checkMap_append _ _ _ _ _ VSquare.check17 (checkMap_append _ _ _ _ _ VSquare.check18 (checkMap_append _ _ _ _ _ VSquare.check19 (checkMap_append _ _ _ _ _ VSquare.check20 (checkMap_append _ _ _ _ _ VSquare.check21 (checkMap_append _ _ _ _ _ VSquare.check22 (checkMap_append _ _ _ _ _ VSquare.check23 (checkMap_append _ _ _ _ _ VSquare.check24 (checkMap_append _ _ _ _ _ VSquare.check25 (checkMap_append _ _ _ _ _ VSquare.check26 (checkMap_append _ _ _ _ _ VSquare.check27 (checkMap_append _ _ _ _ _ VSquare.check28 (checkMap_append _ _ _ _ _ VSquare.check29 (checkMap_append _ _ _ _ _ VSquare.check30 (checkMap_append _ _ _ _ _ VSquare.check31 (checkMap_append _ _ _ _ _ VSquare.check32 (checkMap_append _ _ _ _ _ VSquare.check33 (checkMap_append _ _ _ _ _ VSquare.check34 (checkMap_append _ _ _ _ _ VSquare.check35 (checkMap_append _ _ _ _ _ VSquare.check36 (checkMap_append _ _ _ _ _ VSquare.check37 (checkMap_append _ _ _ _ _ VSquare.check38 (checkMap_append _ _ _ _ _ VSquare.check39 (checkMap_append _ _ _ _ _ VSquare.check40 (checkMap_append _ _ _ _ _ VSquare.check41 (checkMap_append _ _ _ _ _ VSquare.check42 (checkMap_append _ _ _ _ _ VSquare.check43 (checkMap_append _ _ _ _ _ VSquare.check44 VSquare.check45)))))))))))))))))))))))))))))))))))))))))))))
  simpa only [Data.vRows, Data.v2Rows, List.append_assoc] using h

theorem v_square : Data.v * Data.v = Data.v2 := by
  have h := checked_product Data.vRows Data.vRows Data.v2Rows WideV.rows
    Data.vRows_length Data.vRows_length WideV.rows_eq v_square_check
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
