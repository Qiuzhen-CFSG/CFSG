module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.UCubeChecks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideU

/-!
# The literal product U2 * U

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

private theorem u_cube_check :
    checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u2Rows Data.u3Rows = true := by
  have h := (checkMap_append _ _ _ _ _ UCube.check00 (checkMap_append _ _ _ _ _ UCube.check01 (checkMap_append _ _ _ _ _ UCube.check02 (checkMap_append _ _ _ _ _ UCube.check03 (checkMap_append _ _ _ _ _ UCube.check04 (checkMap_append _ _ _ _ _ UCube.check05 (checkMap_append _ _ _ _ _ UCube.check06 (checkMap_append _ _ _ _ _ UCube.check07 (checkMap_append _ _ _ _ _ UCube.check08 (checkMap_append _ _ _ _ _ UCube.check09 (checkMap_append _ _ _ _ _ UCube.check10 (checkMap_append _ _ _ _ _ UCube.check11 (checkMap_append _ _ _ _ _ UCube.check12 (checkMap_append _ _ _ _ _ UCube.check13 (checkMap_append _ _ _ _ _ UCube.check14 (checkMap_append _ _ _ _ _ UCube.check15 (checkMap_append _ _ _ _ _ UCube.check16 (checkMap_append _ _ _ _ _ UCube.check17 (checkMap_append _ _ _ _ _ UCube.check18 (checkMap_append _ _ _ _ _ UCube.check19 (checkMap_append _ _ _ _ _ UCube.check20 (checkMap_append _ _ _ _ _ UCube.check21 (checkMap_append _ _ _ _ _ UCube.check22 (checkMap_append _ _ _ _ _ UCube.check23 (checkMap_append _ _ _ _ _ UCube.check24 (checkMap_append _ _ _ _ _ UCube.check25 (checkMap_append _ _ _ _ _ UCube.check26 (checkMap_append _ _ _ _ _ UCube.check27 (checkMap_append _ _ _ _ _ UCube.check28 (checkMap_append _ _ _ _ _ UCube.check29 (checkMap_append _ _ _ _ _ UCube.check30 (checkMap_append _ _ _ _ _ UCube.check31 (checkMap_append _ _ _ _ _ UCube.check32 (checkMap_append _ _ _ _ _ UCube.check33 (checkMap_append _ _ _ _ _ UCube.check34 (checkMap_append _ _ _ _ _ UCube.check35 (checkMap_append _ _ _ _ _ UCube.check36 (checkMap_append _ _ _ _ _ UCube.check37 (checkMap_append _ _ _ _ _ UCube.check38 (checkMap_append _ _ _ _ _ UCube.check39 (checkMap_append _ _ _ _ _ UCube.check40 (checkMap_append _ _ _ _ _ UCube.check41 (checkMap_append _ _ _ _ _ UCube.check42 (checkMap_append _ _ _ _ _ UCube.check43 (checkMap_append _ _ _ _ _ UCube.check44 UCube.check45)))))))))))))))))))))))))))))))))))))))))))))
  simpa only [Data.u2Rows, Data.u3Rows, List.append_assoc] using h

theorem u_cube : Data.u2 * Data.u = Data.u3 := by
  have h := checked_product Data.u2Rows Data.uRows Data.u3Rows WideU.rows
    Data.u2Rows_length Data.uRows_length WideU.rows_eq u_cube_check
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords
