module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_196608 : Path.checkChunk context decode facts instructions 196608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_197120 : Path.checkChunk context decode facts instructions 197120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_197632 : Path.checkChunk context decode facts instructions 197632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_198144 : Path.checkChunk context decode facts instructions 198144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_198656 : Path.checkChunk context decode facts instructions 198656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_199168 : Path.checkChunk context decode facts instructions 199168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_199680 : Path.checkChunk context decode facts instructions 199680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_200192 : Path.checkChunk context decode facts instructions 200192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_200704 : Path.checkChunk context decode facts instructions 200704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_201216 : Path.checkChunk context decode facts instructions 201216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_201728 : Path.checkChunk context decode facts instructions 201728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_202240 : Path.checkChunk context decode facts instructions 202240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_202752 : Path.checkChunk context decode facts instructions 202752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_203264 : Path.checkChunk context decode facts instructions 203264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_203776 : Path.checkChunk context decode facts instructions 203776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_204288 : Path.checkChunk context decode facts instructions 204288 512 = true := by
  decide +kernel

theorem sound_196608 (prior : ∀ n, n < 196608 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 204800 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h197120 := Path.chunk_sound context_valid decode facts instructions 196608 512
    prior checked_196608
  have h197632 := Path.chunk_sound context_valid decode facts instructions 197120 512
    h197120 checked_197120
  have h198144 := Path.chunk_sound context_valid decode facts instructions 197632 512
    h197632 checked_197632
  have h198656 := Path.chunk_sound context_valid decode facts instructions 198144 512
    h198144 checked_198144
  have h199168 := Path.chunk_sound context_valid decode facts instructions 198656 512
    h198656 checked_198656
  have h199680 := Path.chunk_sound context_valid decode facts instructions 199168 512
    h199168 checked_199168
  have h200192 := Path.chunk_sound context_valid decode facts instructions 199680 512
    h199680 checked_199680
  have h200704 := Path.chunk_sound context_valid decode facts instructions 200192 512
    h200192 checked_200192
  have h201216 := Path.chunk_sound context_valid decode facts instructions 200704 512
    h200704 checked_200704
  have h201728 := Path.chunk_sound context_valid decode facts instructions 201216 512
    h201216 checked_201216
  have h202240 := Path.chunk_sound context_valid decode facts instructions 201728 512
    h201728 checked_201728
  have h202752 := Path.chunk_sound context_valid decode facts instructions 202240 512
    h202240 checked_202240
  have h203264 := Path.chunk_sound context_valid decode facts instructions 202752 512
    h202752 checked_202752
  have h203776 := Path.chunk_sound context_valid decode facts instructions 203264 512
    h203264 checked_203264
  have h204288 := Path.chunk_sound context_valid decode facts instructions 203776 512
    h203776 checked_203776
  have h204800 := Path.chunk_sound context_valid decode facts instructions 204288 512
    h204288 checked_204288
  exact h204800

end Sporadic.Janko3.AmalgamPresentation.Cover
