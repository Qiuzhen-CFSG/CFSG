module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1228800 : Path.checkChunk context decode facts instructions 1228800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1229312 : Path.checkChunk context decode facts instructions 1229312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1229824 : Path.checkChunk context decode facts instructions 1229824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1230336 : Path.checkChunk context decode facts instructions 1230336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1230848 : Path.checkChunk context decode facts instructions 1230848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1231360 : Path.checkChunk context decode facts instructions 1231360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1231872 : Path.checkChunk context decode facts instructions 1231872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1232384 : Path.checkChunk context decode facts instructions 1232384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1232896 : Path.checkChunk context decode facts instructions 1232896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1233408 : Path.checkChunk context decode facts instructions 1233408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1233920 : Path.checkChunk context decode facts instructions 1233920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1234432 : Path.checkChunk context decode facts instructions 1234432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1234944 : Path.checkChunk context decode facts instructions 1234944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1235456 : Path.checkChunk context decode facts instructions 1235456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1235968 : Path.checkChunk context decode facts instructions 1235968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1236480 : Path.checkChunk context decode facts instructions 1236480 512 = true := by
  decide +kernel

theorem sound_1228800 (prior : ∀ n, n < 1228800 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1236992 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1229312 := Path.chunk_sound context_valid decode facts instructions 1228800 512
    prior checked_1228800
  have h1229824 := Path.chunk_sound context_valid decode facts instructions 1229312 512
    h1229312 checked_1229312
  have h1230336 := Path.chunk_sound context_valid decode facts instructions 1229824 512
    h1229824 checked_1229824
  have h1230848 := Path.chunk_sound context_valid decode facts instructions 1230336 512
    h1230336 checked_1230336
  have h1231360 := Path.chunk_sound context_valid decode facts instructions 1230848 512
    h1230848 checked_1230848
  have h1231872 := Path.chunk_sound context_valid decode facts instructions 1231360 512
    h1231360 checked_1231360
  have h1232384 := Path.chunk_sound context_valid decode facts instructions 1231872 512
    h1231872 checked_1231872
  have h1232896 := Path.chunk_sound context_valid decode facts instructions 1232384 512
    h1232384 checked_1232384
  have h1233408 := Path.chunk_sound context_valid decode facts instructions 1232896 512
    h1232896 checked_1232896
  have h1233920 := Path.chunk_sound context_valid decode facts instructions 1233408 512
    h1233408 checked_1233408
  have h1234432 := Path.chunk_sound context_valid decode facts instructions 1233920 512
    h1233920 checked_1233920
  have h1234944 := Path.chunk_sound context_valid decode facts instructions 1234432 512
    h1234432 checked_1234432
  have h1235456 := Path.chunk_sound context_valid decode facts instructions 1234944 512
    h1234944 checked_1234944
  have h1235968 := Path.chunk_sound context_valid decode facts instructions 1235456 512
    h1235456 checked_1235456
  have h1236480 := Path.chunk_sound context_valid decode facts instructions 1235968 512
    h1235968 checked_1235968
  have h1236992 := Path.chunk_sound context_valid decode facts instructions 1236480 512
    h1236480 checked_1236480
  exact h1236992

end Sporadic.Janko3.AmalgamPresentation.Cover
