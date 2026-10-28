module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1171456 : Path.checkChunk context decode facts instructions 1171456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1171968 : Path.checkChunk context decode facts instructions 1171968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1172480 : Path.checkChunk context decode facts instructions 1172480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1172992 : Path.checkChunk context decode facts instructions 1172992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1173504 : Path.checkChunk context decode facts instructions 1173504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1174016 : Path.checkChunk context decode facts instructions 1174016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1174528 : Path.checkChunk context decode facts instructions 1174528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1175040 : Path.checkChunk context decode facts instructions 1175040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1175552 : Path.checkChunk context decode facts instructions 1175552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1176064 : Path.checkChunk context decode facts instructions 1176064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1176576 : Path.checkChunk context decode facts instructions 1176576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1177088 : Path.checkChunk context decode facts instructions 1177088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1177600 : Path.checkChunk context decode facts instructions 1177600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1178112 : Path.checkChunk context decode facts instructions 1178112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1178624 : Path.checkChunk context decode facts instructions 1178624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1179136 : Path.checkChunk context decode facts instructions 1179136 512 = true := by
  decide +kernel

theorem sound_1171456 (prior : ∀ n, n < 1171456 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1179648 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1171968 := Path.chunk_sound context_valid decode facts instructions 1171456 512
    prior checked_1171456
  have h1172480 := Path.chunk_sound context_valid decode facts instructions 1171968 512
    h1171968 checked_1171968
  have h1172992 := Path.chunk_sound context_valid decode facts instructions 1172480 512
    h1172480 checked_1172480
  have h1173504 := Path.chunk_sound context_valid decode facts instructions 1172992 512
    h1172992 checked_1172992
  have h1174016 := Path.chunk_sound context_valid decode facts instructions 1173504 512
    h1173504 checked_1173504
  have h1174528 := Path.chunk_sound context_valid decode facts instructions 1174016 512
    h1174016 checked_1174016
  have h1175040 := Path.chunk_sound context_valid decode facts instructions 1174528 512
    h1174528 checked_1174528
  have h1175552 := Path.chunk_sound context_valid decode facts instructions 1175040 512
    h1175040 checked_1175040
  have h1176064 := Path.chunk_sound context_valid decode facts instructions 1175552 512
    h1175552 checked_1175552
  have h1176576 := Path.chunk_sound context_valid decode facts instructions 1176064 512
    h1176064 checked_1176064
  have h1177088 := Path.chunk_sound context_valid decode facts instructions 1176576 512
    h1176576 checked_1176576
  have h1177600 := Path.chunk_sound context_valid decode facts instructions 1177088 512
    h1177088 checked_1177088
  have h1178112 := Path.chunk_sound context_valid decode facts instructions 1177600 512
    h1177600 checked_1177600
  have h1178624 := Path.chunk_sound context_valid decode facts instructions 1178112 512
    h1178112 checked_1178112
  have h1179136 := Path.chunk_sound context_valid decode facts instructions 1178624 512
    h1178624 checked_1178624
  have h1179648 := Path.chunk_sound context_valid decode facts instructions 1179136 512
    h1179136 checked_1179136
  exact h1179648

end Sporadic.Janko3.AmalgamPresentation.Cover
