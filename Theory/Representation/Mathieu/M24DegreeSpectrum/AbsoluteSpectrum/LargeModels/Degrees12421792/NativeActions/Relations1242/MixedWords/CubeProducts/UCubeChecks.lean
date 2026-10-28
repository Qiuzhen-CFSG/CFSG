module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.WideUData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.PrefixData

/-!
# Kernel checks for U2 * U

All 1242 row equations use the proved carry-free accumulation and
balanced compression, with no increased resource limits.
Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0 matrices.
See `CubeProducts/source/README.md` for conventions and validation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.UCube

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

set_option Elab.async false

theorem check00 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u200 (Data.u300) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check01 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u201 (Data.u301) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check02 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u202 (Data.u302) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check03 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u203 (Data.u303) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check04 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u204 (Data.u304) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check05 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u205 (Data.u305) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check06 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u206 (Data.u306) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check07 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u207 (Data.u307) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check08 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u208 (Data.u308) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check09 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u209 (Data.u309) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check10 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u210 (Data.u310) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check11 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u211 (Data.u311) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check12 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u212 (Data.u312) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check13 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u213 (Data.u313) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check14 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u214 (Data.u314) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check15 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u215 (Data.u315) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check16 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u216 (Data.u316) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check17 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u217 (Data.u317) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check18 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u218 (Data.u318) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check19 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u219 (Data.u319) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check20 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u220 (Data.u320) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check21 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u221 (Data.u321) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check22 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u222 (Data.u322) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check23 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u223 (Data.u323) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check24 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u224 (Data.u324) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check25 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u225 (Data.u325) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check26 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u226 (Data.u326) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check27 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u227 (Data.u327) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check28 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u228 (Data.u328) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check29 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u229 (Data.u329) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check30 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u230 (Data.u330) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check31 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u231 (Data.u331) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check32 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u232 (Data.u332) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check33 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u233 (Data.u333) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check34 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u234 (Data.u334) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check35 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u235 (Data.u335) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check36 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u236 (Data.u336) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check37 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u237 (Data.u337) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check38 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u238 (Data.u338) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check39 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u239 (Data.u339) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check40 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u240 (Data.u340) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check41 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u241 (Data.u341) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check42 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u242 (Data.u342) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check43 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u243 (Data.u343) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check44 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u244 (Data.u344) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

theorem check45 : checkMap (fun a => compressTree 6 1242 (accumChunks a WideU.rows)) Data.u245 (Data.u345) = true := by
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
  · decide +kernel
  apply checkMap_cons
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

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords.CubeProducts.UCube
