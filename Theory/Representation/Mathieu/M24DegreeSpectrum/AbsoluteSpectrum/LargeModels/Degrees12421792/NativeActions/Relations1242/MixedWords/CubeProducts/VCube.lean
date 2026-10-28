module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.VCubeChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV

/-!
# The literal product V2 * V

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

private theorem v_cube_check :
    checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v2Rows Data.v3Rows = true := by
  have h := (checkMap_append _ _ _ _ _ VCube.check00 (checkMap_append _ _ _ _ _ VCube.check01 (checkMap_append _ _ _ _ _ VCube.check02 (checkMap_append _ _ _ _ _ VCube.check03 (checkMap_append _ _ _ _ _ VCube.check04 (checkMap_append _ _ _ _ _ VCube.check05 (checkMap_append _ _ _ _ _ VCube.check06 (checkMap_append _ _ _ _ _ VCube.check07 (checkMap_append _ _ _ _ _ VCube.check08 (checkMap_append _ _ _ _ _ VCube.check09 (checkMap_append _ _ _ _ _ VCube.check10 (checkMap_append _ _ _ _ _ VCube.check11 (checkMap_append _ _ _ _ _ VCube.check12 (checkMap_append _ _ _ _ _ VCube.check13 (checkMap_append _ _ _ _ _ VCube.check14 (checkMap_append _ _ _ _ _ VCube.check15 (checkMap_append _ _ _ _ _ VCube.check16 (checkMap_append _ _ _ _ _ VCube.check17 (checkMap_append _ _ _ _ _ VCube.check18 (checkMap_append _ _ _ _ _ VCube.check19 (checkMap_append _ _ _ _ _ VCube.check20 (checkMap_append _ _ _ _ _ VCube.check21 (checkMap_append _ _ _ _ _ VCube.check22 (checkMap_append _ _ _ _ _ VCube.check23 (checkMap_append _ _ _ _ _ VCube.check24 (checkMap_append _ _ _ _ _ VCube.check25 (checkMap_append _ _ _ _ _ VCube.check26 (checkMap_append _ _ _ _ _ VCube.check27 (checkMap_append _ _ _ _ _ VCube.check28 (checkMap_append _ _ _ _ _ VCube.check29 (checkMap_append _ _ _ _ _ VCube.check30 (checkMap_append _ _ _ _ _ VCube.check31 (checkMap_append _ _ _ _ _ VCube.check32 (checkMap_append _ _ _ _ _ VCube.check33 (checkMap_append _ _ _ _ _ VCube.check34 (checkMap_append _ _ _ _ _ VCube.check35 (checkMap_append _ _ _ _ _ VCube.check36 (checkMap_append _ _ _ _ _ VCube.check37 (checkMap_append _ _ _ _ _ VCube.check38 (checkMap_append _ _ _ _ _ VCube.check39 (checkMap_append _ _ _ _ _ VCube.check40 (checkMap_append _ _ _ _ _ VCube.check41 (checkMap_append _ _ _ _ _ VCube.check42 (checkMap_append _ _ _ _ _ VCube.check43 (checkMap_append _ _ _ _ _ VCube.check44 VCube.check45)))))))))))))))))))))))))))))))))))))))))))))
  simpa only [Data.v2Rows, Data.v3Rows, List.append_assoc] using h

theorem v_cube : Data.v2 * Data.v = Data.v3 := by
  have h := checked_product Data.v2Rows Data.vRows Data.v3Rows WideV.rows
    Data.v2Rows_length Data.vRows_length WideV.rows_eq v_cube_check
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
