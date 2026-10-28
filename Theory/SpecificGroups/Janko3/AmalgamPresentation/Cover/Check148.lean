module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1212416 : Path.checkChunk context decode facts instructions 1212416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1212928 : Path.checkChunk context decode facts instructions 1212928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1213440 : Path.checkChunk context decode facts instructions 1213440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1213952 : Path.checkChunk context decode facts instructions 1213952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1214464 : Path.checkChunk context decode facts instructions 1214464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1214976 : Path.checkChunk context decode facts instructions 1214976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1215488 : Path.checkChunk context decode facts instructions 1215488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1216000 : Path.checkChunk context decode facts instructions 1216000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1216512 : Path.checkChunk context decode facts instructions 1216512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1217024 : Path.checkChunk context decode facts instructions 1217024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1217536 : Path.checkChunk context decode facts instructions 1217536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1218048 : Path.checkChunk context decode facts instructions 1218048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1218560 : Path.checkChunk context decode facts instructions 1218560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1219072 : Path.checkChunk context decode facts instructions 1219072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1219584 : Path.checkChunk context decode facts instructions 1219584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1220096 : Path.checkChunk context decode facts instructions 1220096 512 = true := by
  decide +kernel

theorem sound_1212416 (prior : ∀ n, n < 1212416 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1220608 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1212928 := Path.chunk_sound context_valid decode facts instructions 1212416 512
    prior checked_1212416
  have h1213440 := Path.chunk_sound context_valid decode facts instructions 1212928 512
    h1212928 checked_1212928
  have h1213952 := Path.chunk_sound context_valid decode facts instructions 1213440 512
    h1213440 checked_1213440
  have h1214464 := Path.chunk_sound context_valid decode facts instructions 1213952 512
    h1213952 checked_1213952
  have h1214976 := Path.chunk_sound context_valid decode facts instructions 1214464 512
    h1214464 checked_1214464
  have h1215488 := Path.chunk_sound context_valid decode facts instructions 1214976 512
    h1214976 checked_1214976
  have h1216000 := Path.chunk_sound context_valid decode facts instructions 1215488 512
    h1215488 checked_1215488
  have h1216512 := Path.chunk_sound context_valid decode facts instructions 1216000 512
    h1216000 checked_1216000
  have h1217024 := Path.chunk_sound context_valid decode facts instructions 1216512 512
    h1216512 checked_1216512
  have h1217536 := Path.chunk_sound context_valid decode facts instructions 1217024 512
    h1217024 checked_1217024
  have h1218048 := Path.chunk_sound context_valid decode facts instructions 1217536 512
    h1217536 checked_1217536
  have h1218560 := Path.chunk_sound context_valid decode facts instructions 1218048 512
    h1218048 checked_1218048
  have h1219072 := Path.chunk_sound context_valid decode facts instructions 1218560 512
    h1218560 checked_1218560
  have h1219584 := Path.chunk_sound context_valid decode facts instructions 1219072 512
    h1219072 checked_1219072
  have h1220096 := Path.chunk_sound context_valid decode facts instructions 1219584 512
    h1219584 checked_1219584
  have h1220608 := Path.chunk_sound context_valid decode facts instructions 1220096 512
    h1220096 checked_1220096
  exact h1220608

end Sporadic.Janko3.AmalgamPresentation.Cover
