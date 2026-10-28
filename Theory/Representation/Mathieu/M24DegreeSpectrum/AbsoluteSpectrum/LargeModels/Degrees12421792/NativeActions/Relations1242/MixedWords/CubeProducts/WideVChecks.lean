module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideVData

/-!
# Kernel checks for the widened V rows

Separate row proofs bound the kernel work. Synchronous elaboration keeps
the active certificate count bounded without changing Lean thread settings.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

set_option Elab.async false

theorem check00 : checkMap (expandTree 6 1242) Data.v00 (rows00) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check01 : checkMap (expandTree 6 1242) Data.v01 (rows01) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check02 : checkMap (expandTree 6 1242) Data.v02 (rows02) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check03 : checkMap (expandTree 6 1242) Data.v03 (rows03) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check04 : checkMap (expandTree 6 1242) Data.v04 (rows04) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check05 : checkMap (expandTree 6 1242) Data.v05 (rows05) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check06 : checkMap (expandTree 6 1242) Data.v06 (rows06) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check07 : checkMap (expandTree 6 1242) Data.v07 (rows07) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check08 : checkMap (expandTree 6 1242) Data.v08 (rows08) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check09 : checkMap (expandTree 6 1242) Data.v09 (rows09) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check10 : checkMap (expandTree 6 1242) Data.v10 (rows10) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check11 : checkMap (expandTree 6 1242) Data.v11 (rows11) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check12 : checkMap (expandTree 6 1242) Data.v12 (rows12) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check13 : checkMap (expandTree 6 1242) Data.v13 (rows13) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check14 : checkMap (expandTree 6 1242) Data.v14 (rows14) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check15 : checkMap (expandTree 6 1242) Data.v15 (rows15) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check16 : checkMap (expandTree 6 1242) Data.v16 (rows16) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check17 : checkMap (expandTree 6 1242) Data.v17 (rows17) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check18 : checkMap (expandTree 6 1242) Data.v18 (rows18) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check19 : checkMap (expandTree 6 1242) Data.v19 (rows19) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check20 : checkMap (expandTree 6 1242) Data.v20 (rows20) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check21 : checkMap (expandTree 6 1242) Data.v21 (rows21) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check22 : checkMap (expandTree 6 1242) Data.v22 (rows22) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check23 : checkMap (expandTree 6 1242) Data.v23 (rows23) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check24 : checkMap (expandTree 6 1242) Data.v24 (rows24) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check25 : checkMap (expandTree 6 1242) Data.v25 (rows25) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check26 : checkMap (expandTree 6 1242) Data.v26 (rows26) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check27 : checkMap (expandTree 6 1242) Data.v27 (rows27) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check28 : checkMap (expandTree 6 1242) Data.v28 (rows28) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check29 : checkMap (expandTree 6 1242) Data.v29 (rows29) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check30 : checkMap (expandTree 6 1242) Data.v30 (rows30) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check31 : checkMap (expandTree 6 1242) Data.v31 (rows31) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check32 : checkMap (expandTree 6 1242) Data.v32 (rows32) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check33 : checkMap (expandTree 6 1242) Data.v33 (rows33) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check34 : checkMap (expandTree 6 1242) Data.v34 (rows34) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check35 : checkMap (expandTree 6 1242) Data.v35 (rows35) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check36 : checkMap (expandTree 6 1242) Data.v36 (rows36) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check37 : checkMap (expandTree 6 1242) Data.v37 (rows37) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check38 : checkMap (expandTree 6 1242) Data.v38 (rows38) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check39 : checkMap (expandTree 6 1242) Data.v39 (rows39) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check40 : checkMap (expandTree 6 1242) Data.v40 (rows40) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check41 : checkMap (expandTree 6 1242) Data.v41 (rows41) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check42 : checkMap (expandTree 6 1242) Data.v42 (rows42) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check43 : checkMap (expandTree 6 1242) Data.v43 (rows43) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check44 : checkMap (expandTree 6 1242) Data.v44 (rows44) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check45 : checkMap (expandTree 6 1242) Data.v45 (rows45) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideV
