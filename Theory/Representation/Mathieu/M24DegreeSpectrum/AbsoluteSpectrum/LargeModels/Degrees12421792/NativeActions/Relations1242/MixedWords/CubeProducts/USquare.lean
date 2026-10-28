module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.USquareChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideU

/-!
# The literal product U * U

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

private theorem u_square_check :
    checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.uRows Data.u2Rows = true := by
  have h := (checkMap_append _ _ _ _ _ USquare.check00 (checkMap_append _ _ _ _ _ USquare.check01 (checkMap_append _ _ _ _ _ USquare.check02 (checkMap_append _ _ _ _ _ USquare.check03 (checkMap_append _ _ _ _ _ USquare.check04 (checkMap_append _ _ _ _ _ USquare.check05 (checkMap_append _ _ _ _ _ USquare.check06 (checkMap_append _ _ _ _ _ USquare.check07 (checkMap_append _ _ _ _ _ USquare.check08 (checkMap_append _ _ _ _ _ USquare.check09 (checkMap_append _ _ _ _ _ USquare.check10 (checkMap_append _ _ _ _ _ USquare.check11 (checkMap_append _ _ _ _ _ USquare.check12 (checkMap_append _ _ _ _ _ USquare.check13 (checkMap_append _ _ _ _ _ USquare.check14 (checkMap_append _ _ _ _ _ USquare.check15 (checkMap_append _ _ _ _ _ USquare.check16 (checkMap_append _ _ _ _ _ USquare.check17 (checkMap_append _ _ _ _ _ USquare.check18 (checkMap_append _ _ _ _ _ USquare.check19 (checkMap_append _ _ _ _ _ USquare.check20 (checkMap_append _ _ _ _ _ USquare.check21 (checkMap_append _ _ _ _ _ USquare.check22 (checkMap_append _ _ _ _ _ USquare.check23 (checkMap_append _ _ _ _ _ USquare.check24 (checkMap_append _ _ _ _ _ USquare.check25 (checkMap_append _ _ _ _ _ USquare.check26 (checkMap_append _ _ _ _ _ USquare.check27 (checkMap_append _ _ _ _ _ USquare.check28 (checkMap_append _ _ _ _ _ USquare.check29 (checkMap_append _ _ _ _ _ USquare.check30 (checkMap_append _ _ _ _ _ USquare.check31 (checkMap_append _ _ _ _ _ USquare.check32 (checkMap_append _ _ _ _ _ USquare.check33 (checkMap_append _ _ _ _ _ USquare.check34 (checkMap_append _ _ _ _ _ USquare.check35 (checkMap_append _ _ _ _ _ USquare.check36 (checkMap_append _ _ _ _ _ USquare.check37 (checkMap_append _ _ _ _ _ USquare.check38 (checkMap_append _ _ _ _ _ USquare.check39 (checkMap_append _ _ _ _ _ USquare.check40 (checkMap_append _ _ _ _ _ USquare.check41 (checkMap_append _ _ _ _ _ USquare.check42 (checkMap_append _ _ _ _ _ USquare.check43 (checkMap_append _ _ _ _ _ USquare.check44 USquare.check45)))))))))))))))))))))))))))))))))))))))))))))
  simpa only [Data.uRows, Data.u2Rows, List.append_assoc] using h

theorem u_square : Data.u * Data.u = Data.u2 := by
  have h := checked_product Data.uRows Data.uRows Data.u2Rows WideU.rows
    Data.uRows_length Data.uRows_length WideU.rows_eq u_square_check
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
