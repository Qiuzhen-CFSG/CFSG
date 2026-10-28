module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV3Data

/-!
# Kernel checks for the widened V3 rows

Separate row proofs bound the kernel work. Synchronous elaboration keeps
the active certificate count bounded without changing Lean thread settings.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV3

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

set_option Elab.async false

theorem check00 : checkMap (expandTree 6 1242) Data.v300 (rows00) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check01 : checkMap (expandTree 6 1242) Data.v301 (rows01) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check02 : checkMap (expandTree 6 1242) Data.v302 (rows02) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check03 : checkMap (expandTree 6 1242) Data.v303 (rows03) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check04 : checkMap (expandTree 6 1242) Data.v304 (rows04) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check05 : checkMap (expandTree 6 1242) Data.v305 (rows05) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check06 : checkMap (expandTree 6 1242) Data.v306 (rows06) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check07 : checkMap (expandTree 6 1242) Data.v307 (rows07) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check08 : checkMap (expandTree 6 1242) Data.v308 (rows08) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check09 : checkMap (expandTree 6 1242) Data.v309 (rows09) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check10 : checkMap (expandTree 6 1242) Data.v310 (rows10) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check11 : checkMap (expandTree 6 1242) Data.v311 (rows11) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check12 : checkMap (expandTree 6 1242) Data.v312 (rows12) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check13 : checkMap (expandTree 6 1242) Data.v313 (rows13) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check14 : checkMap (expandTree 6 1242) Data.v314 (rows14) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check15 : checkMap (expandTree 6 1242) Data.v315 (rows15) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check16 : checkMap (expandTree 6 1242) Data.v316 (rows16) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check17 : checkMap (expandTree 6 1242) Data.v317 (rows17) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check18 : checkMap (expandTree 6 1242) Data.v318 (rows18) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check19 : checkMap (expandTree 6 1242) Data.v319 (rows19) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check20 : checkMap (expandTree 6 1242) Data.v320 (rows20) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check21 : checkMap (expandTree 6 1242) Data.v321 (rows21) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check22 : checkMap (expandTree 6 1242) Data.v322 (rows22) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check23 : checkMap (expandTree 6 1242) Data.v323 (rows23) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check24 : checkMap (expandTree 6 1242) Data.v324 (rows24) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check25 : checkMap (expandTree 6 1242) Data.v325 (rows25) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check26 : checkMap (expandTree 6 1242) Data.v326 (rows26) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check27 : checkMap (expandTree 6 1242) Data.v327 (rows27) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check28 : checkMap (expandTree 6 1242) Data.v328 (rows28) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check29 : checkMap (expandTree 6 1242) Data.v329 (rows29) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check30 : checkMap (expandTree 6 1242) Data.v330 (rows30) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check31 : checkMap (expandTree 6 1242) Data.v331 (rows31) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check32 : checkMap (expandTree 6 1242) Data.v332 (rows32) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check33 : checkMap (expandTree 6 1242) Data.v333 (rows33) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check34 : checkMap (expandTree 6 1242) Data.v334 (rows34) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check35 : checkMap (expandTree 6 1242) Data.v335 (rows35) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check36 : checkMap (expandTree 6 1242) Data.v336 (rows36) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check37 : checkMap (expandTree 6 1242) Data.v337 (rows37) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check38 : checkMap (expandTree 6 1242) Data.v338 (rows38) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check39 : checkMap (expandTree 6 1242) Data.v339 (rows39) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check40 : checkMap (expandTree 6 1242) Data.v340 (rows40) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check41 : checkMap (expandTree 6 1242) Data.v341 (rows41) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check42 : checkMap (expandTree 6 1242) Data.v342 (rows42) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check43 : checkMap (expandTree 6 1242) Data.v343 (rows43) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check44 : checkMap (expandTree 6 1242) Data.v344 (rows44) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

theorem check45 : checkMap (expandTree 6 1242) Data.v345 (rows45) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV3
