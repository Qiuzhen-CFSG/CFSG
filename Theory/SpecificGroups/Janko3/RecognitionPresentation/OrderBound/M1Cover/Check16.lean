module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Tables

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_262144 : Scan.checkChunk context facts instructions 262144 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_263168 : Scan.checkChunk context facts instructions 263168 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_264192 : Scan.checkChunk context facts instructions 264192 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_265216 : Scan.checkChunk context facts instructions 265216 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_266240 : Scan.checkChunk context facts instructions 266240 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_267264 : Scan.checkChunk context facts instructions 267264 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_268288 : Scan.checkChunk context facts instructions 268288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_269312 : Scan.checkChunk context facts instructions 269312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_270336 : Scan.checkChunk context facts instructions 270336 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_271360 : Scan.checkChunk context facts instructions 271360 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_272384 : Scan.checkChunk context facts instructions 272384 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_273408 : Scan.checkChunk context facts instructions 273408 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_274432 : Scan.checkChunk context facts instructions 274432 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_275456 : Scan.checkChunk context facts instructions 275456 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_276480 : Scan.checkChunk context facts instructions 276480 801 = true := by
  decide +kernel

theorem sound_262144 (prior : ∀ n, n < 262144 →
    Holds M1 generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 277281 → Holds M1 generator (definitions.repr generator) (facts n) := by
  have h263168 := Scan.chunk_sound context_valid facts instructions 262144 1024
    prior checked_262144
  have h264192 := Scan.chunk_sound context_valid facts instructions 263168 1024
    h263168 checked_263168
  have h265216 := Scan.chunk_sound context_valid facts instructions 264192 1024
    h264192 checked_264192
  have h266240 := Scan.chunk_sound context_valid facts instructions 265216 1024
    h265216 checked_265216
  have h267264 := Scan.chunk_sound context_valid facts instructions 266240 1024
    h266240 checked_266240
  have h268288 := Scan.chunk_sound context_valid facts instructions 267264 1024
    h267264 checked_267264
  have h269312 := Scan.chunk_sound context_valid facts instructions 268288 1024
    h268288 checked_268288
  have h270336 := Scan.chunk_sound context_valid facts instructions 269312 1024
    h269312 checked_269312
  have h271360 := Scan.chunk_sound context_valid facts instructions 270336 1024
    h270336 checked_270336
  have h272384 := Scan.chunk_sound context_valid facts instructions 271360 1024
    h271360 checked_271360
  have h273408 := Scan.chunk_sound context_valid facts instructions 272384 1024
    h272384 checked_272384
  have h274432 := Scan.chunk_sound context_valid facts instructions 273408 1024
    h273408 checked_273408
  have h275456 := Scan.chunk_sound context_valid facts instructions 274432 1024
    h274432 checked_274432
  have h276480 := Scan.chunk_sound context_valid facts instructions 275456 1024
    h275456 checked_275456
  have h277281 := Scan.chunk_sound context_valid facts instructions 276480 801
    h276480 checked_276480
  exact h277281

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
