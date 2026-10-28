module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideVChecks

/-!
# Certified radix expansion of V

Concatenating the independent row checks proves the entire widened table
is the expansion of the fixed binary matrix.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

theorem rows_eq : rows.flatten = Data.vRows.map (expandTree 6 1242) := by
  have h := (checkMap_append _ _ _ _ _ check00 (checkMap_append _ _ _ _ _ check01 (checkMap_append _ _ _ _ _ check02 (checkMap_append _ _ _ _ _ check03 (checkMap_append _ _ _ _ _ check04 (checkMap_append _ _ _ _ _ check05 (checkMap_append _ _ _ _ _ check06 (checkMap_append _ _ _ _ _ check07 (checkMap_append _ _ _ _ _ check08 (checkMap_append _ _ _ _ _ check09 (checkMap_append _ _ _ _ _ check10 (checkMap_append _ _ _ _ _ check11 (checkMap_append _ _ _ _ _ check12 (checkMap_append _ _ _ _ _ check13 (checkMap_append _ _ _ _ _ check14 (checkMap_append _ _ _ _ _ check15 (checkMap_append _ _ _ _ _ check16 (checkMap_append _ _ _ _ _ check17 (checkMap_append _ _ _ _ _ check18 (checkMap_append _ _ _ _ _ check19 (checkMap_append _ _ _ _ _ check20 (checkMap_append _ _ _ _ _ check21 (checkMap_append _ _ _ _ _ check22 (checkMap_append _ _ _ _ _ check23 (checkMap_append _ _ _ _ _ check24 (checkMap_append _ _ _ _ _ check25 (checkMap_append _ _ _ _ _ check26 (checkMap_append _ _ _ _ _ check27 (checkMap_append _ _ _ _ _ check28 (checkMap_append _ _ _ _ _ check29 (checkMap_append _ _ _ _ _ check30 (checkMap_append _ _ _ _ _ check31 (checkMap_append _ _ _ _ _ check32 (checkMap_append _ _ _ _ _ check33 (checkMap_append _ _ _ _ _ check34 (checkMap_append _ _ _ _ _ check35 (checkMap_append _ _ _ _ _ check36 (checkMap_append _ _ _ _ _ check37 (checkMap_append _ _ _ _ _ check38 (checkMap_append _ _ _ _ _ check39 (checkMap_append _ _ _ _ _ check40 (checkMap_append _ _ _ _ _ check41 (checkMap_append _ _ _ _ _ check42 (checkMap_append _ _ _ _ _ check43 (checkMap_append _ _ _ _ _ check44 check45)))))))))))))))))))))))))))))))))))))))))))))
  have hc : checkMap (expandTree 6 1242) Data.vRows rows.flatten = true := by
    simpa only [rows, List.flatten_cons, List.flatten_nil, List.append_nil,
      Data.vRows, List.append_assoc] using h
  exact (checkMap_sound _ _ _ hc).symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV
