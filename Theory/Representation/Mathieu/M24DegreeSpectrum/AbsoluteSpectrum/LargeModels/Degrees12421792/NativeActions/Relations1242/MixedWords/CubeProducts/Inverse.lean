module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.InverseChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV3

/-!
# The literal product U3 * V3

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

private theorem cube_inverse_check :
    checkMap (fun a => compressTree 6 1242 (accumChunks a WideV3.rows)) Data.u3Rows Identity.rows = true := by
  have h := (checkMap_append _ _ _ _ _ Inverse.check00 (checkMap_append _ _ _ _ _ Inverse.check01 (checkMap_append _ _ _ _ _ Inverse.check02 (checkMap_append _ _ _ _ _ Inverse.check03 (checkMap_append _ _ _ _ _ Inverse.check04 (checkMap_append _ _ _ _ _ Inverse.check05 (checkMap_append _ _ _ _ _ Inverse.check06 (checkMap_append _ _ _ _ _ Inverse.check07 (checkMap_append _ _ _ _ _ Inverse.check08 (checkMap_append _ _ _ _ _ Inverse.check09 (checkMap_append _ _ _ _ _ Inverse.check10 (checkMap_append _ _ _ _ _ Inverse.check11 (checkMap_append _ _ _ _ _ Inverse.check12 (checkMap_append _ _ _ _ _ Inverse.check13 (checkMap_append _ _ _ _ _ Inverse.check14 (checkMap_append _ _ _ _ _ Inverse.check15 (checkMap_append _ _ _ _ _ Inverse.check16 (checkMap_append _ _ _ _ _ Inverse.check17 (checkMap_append _ _ _ _ _ Inverse.check18 (checkMap_append _ _ _ _ _ Inverse.check19 (checkMap_append _ _ _ _ _ Inverse.check20 (checkMap_append _ _ _ _ _ Inverse.check21 (checkMap_append _ _ _ _ _ Inverse.check22 (checkMap_append _ _ _ _ _ Inverse.check23 (checkMap_append _ _ _ _ _ Inverse.check24 (checkMap_append _ _ _ _ _ Inverse.check25 (checkMap_append _ _ _ _ _ Inverse.check26 (checkMap_append _ _ _ _ _ Inverse.check27 (checkMap_append _ _ _ _ _ Inverse.check28 (checkMap_append _ _ _ _ _ Inverse.check29 (checkMap_append _ _ _ _ _ Inverse.check30 (checkMap_append _ _ _ _ _ Inverse.check31 (checkMap_append _ _ _ _ _ Inverse.check32 (checkMap_append _ _ _ _ _ Inverse.check33 (checkMap_append _ _ _ _ _ Inverse.check34 (checkMap_append _ _ _ _ _ Inverse.check35 (checkMap_append _ _ _ _ _ Inverse.check36 (checkMap_append _ _ _ _ _ Inverse.check37 (checkMap_append _ _ _ _ _ Inverse.check38 (checkMap_append _ _ _ _ _ Inverse.check39 (checkMap_append _ _ _ _ _ Inverse.check40 (checkMap_append _ _ _ _ _ Inverse.check41 (checkMap_append _ _ _ _ _ Inverse.check42 (checkMap_append _ _ _ _ _ Inverse.check43 (checkMap_append _ _ _ _ _ Inverse.check44 Inverse.check45)))))))))))))))))))))))))))))))))))))))))))))
  simpa only [Data.u3Rows, Identity.rows_blocks, List.append_assoc] using h

theorem cube_inverse : Data.u3 * Data.v3 = 1 := by
  have h := checked_product Data.u3Rows Data.v3Rows Identity.rows WideV3.rows
    Data.u3Rows_length Data.v3Rows_length WideV3.rows_eq cube_inverse_check
  simpa only [Data.u3, Data.v3, Identity.decode_rows] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
