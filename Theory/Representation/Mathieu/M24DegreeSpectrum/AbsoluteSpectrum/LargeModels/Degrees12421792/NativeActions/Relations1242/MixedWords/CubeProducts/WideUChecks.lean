module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideUData

/-!
# Kernel checks for the widened U rows

Separate row proofs bound the kernel work. Synchronous elaboration keeps
the active certificate count bounded without changing Lean thread settings.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideU

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

set_option Elab.async false

theorem check00 : checkMap (expandTree 6 1242) Data.u00 (rows00) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check01 : checkMap (expandTree 6 1242) Data.u01 (rows01) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check02 : checkMap (expandTree 6 1242) Data.u02 (rows02) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check03 : checkMap (expandTree 6 1242) Data.u03 (rows03) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check04 : checkMap (expandTree 6 1242) Data.u04 (rows04) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check05 : checkMap (expandTree 6 1242) Data.u05 (rows05) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check06 : checkMap (expandTree 6 1242) Data.u06 (rows06) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check07 : checkMap (expandTree 6 1242) Data.u07 (rows07) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check08 : checkMap (expandTree 6 1242) Data.u08 (rows08) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check09 : checkMap (expandTree 6 1242) Data.u09 (rows09) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check10 : checkMap (expandTree 6 1242) Data.u10 (rows10) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check11 : checkMap (expandTree 6 1242) Data.u11 (rows11) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check12 : checkMap (expandTree 6 1242) Data.u12 (rows12) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check13 : checkMap (expandTree 6 1242) Data.u13 (rows13) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check14 : checkMap (expandTree 6 1242) Data.u14 (rows14) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check15 : checkMap (expandTree 6 1242) Data.u15 (rows15) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check16 : checkMap (expandTree 6 1242) Data.u16 (rows16) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check17 : checkMap (expandTree 6 1242) Data.u17 (rows17) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check18 : checkMap (expandTree 6 1242) Data.u18 (rows18) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check19 : checkMap (expandTree 6 1242) Data.u19 (rows19) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check20 : checkMap (expandTree 6 1242) Data.u20 (rows20) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check21 : checkMap (expandTree 6 1242) Data.u21 (rows21) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check22 : checkMap (expandTree 6 1242) Data.u22 (rows22) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check23 : checkMap (expandTree 6 1242) Data.u23 (rows23) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check24 : checkMap (expandTree 6 1242) Data.u24 (rows24) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check25 : checkMap (expandTree 6 1242) Data.u25 (rows25) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check26 : checkMap (expandTree 6 1242) Data.u26 (rows26) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check27 : checkMap (expandTree 6 1242) Data.u27 (rows27) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check28 : checkMap (expandTree 6 1242) Data.u28 (rows28) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check29 : checkMap (expandTree 6 1242) Data.u29 (rows29) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check30 : checkMap (expandTree 6 1242) Data.u30 (rows30) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check31 : checkMap (expandTree 6 1242) Data.u31 (rows31) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check32 : checkMap (expandTree 6 1242) Data.u32 (rows32) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check33 : checkMap (expandTree 6 1242) Data.u33 (rows33) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check34 : checkMap (expandTree 6 1242) Data.u34 (rows34) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check35 : checkMap (expandTree 6 1242) Data.u35 (rows35) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check36 : checkMap (expandTree 6 1242) Data.u36 (rows36) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check37 : checkMap (expandTree 6 1242) Data.u37 (rows37) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check38 : checkMap (expandTree 6 1242) Data.u38 (rows38) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check39 : checkMap (expandTree 6 1242) Data.u39 (rows39) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check40 : checkMap (expandTree 6 1242) Data.u40 (rows40) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check41 : checkMap (expandTree 6 1242) Data.u41 (rows41) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check42 : checkMap (expandTree 6 1242) Data.u42 (rows42) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check43 : checkMap (expandTree 6 1242) Data.u43 (rows43) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check44 : checkMap (expandTree 6 1242) Data.u44 (rows44) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check45 : checkMap (expandTree 6 1242) Data.u45 (rows45) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideU
