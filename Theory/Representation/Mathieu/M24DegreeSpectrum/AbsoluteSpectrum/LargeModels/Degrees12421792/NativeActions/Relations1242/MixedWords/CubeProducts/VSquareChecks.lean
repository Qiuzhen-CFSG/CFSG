module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideVData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixData

/-!
# Kernel checks for V * V

All 1242 row equations use the proved carry-free accumulation and
balanced compression, with no increased resource limits.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.VSquare

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

set_option Elab.async false

theorem check00 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v00 (Data.v200) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check01 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v01 (Data.v201) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check02 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v02 (Data.v202) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check03 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v03 (Data.v203) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check04 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v04 (Data.v204) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check05 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v05 (Data.v205) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check06 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v06 (Data.v206) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check07 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v07 (Data.v207) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check08 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v08 (Data.v208) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check09 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v09 (Data.v209) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check10 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v10 (Data.v210) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check11 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v11 (Data.v211) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check12 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v12 (Data.v212) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check13 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v13 (Data.v213) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check14 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v14 (Data.v214) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check15 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v15 (Data.v215) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check16 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v16 (Data.v216) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check17 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v17 (Data.v217) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check18 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v18 (Data.v218) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check19 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v19 (Data.v219) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check20 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v20 (Data.v220) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check21 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v21 (Data.v221) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check22 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v22 (Data.v222) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check23 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v23 (Data.v223) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check24 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v24 (Data.v224) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check25 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v25 (Data.v225) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check26 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v26 (Data.v226) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check27 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v27 (Data.v227) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check28 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v28 (Data.v228) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check29 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v29 (Data.v229) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check30 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v30 (Data.v230) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check31 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v31 (Data.v231) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check32 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v32 (Data.v232) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check33 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v33 (Data.v233) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check34 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v34 (Data.v234) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check35 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v35 (Data.v235) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check36 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v36 (Data.v236) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check37 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v37 (Data.v237) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check38 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v38 (Data.v238) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check39 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v39 (Data.v239) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check40 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v40 (Data.v240) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check41 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v41 (Data.v241) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check42 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v42 (Data.v242) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check43 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v43 (Data.v243) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check44 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v44 (Data.v244) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check45 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideV.rows)) Data.v45 (Data.v245) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.VSquare
