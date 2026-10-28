module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1220608 : Path.checkChunk context decode facts instructions 1220608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1221120 : Path.checkChunk context decode facts instructions 1221120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1221632 : Path.checkChunk context decode facts instructions 1221632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1222144 : Path.checkChunk context decode facts instructions 1222144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1222656 : Path.checkChunk context decode facts instructions 1222656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1223168 : Path.checkChunk context decode facts instructions 1223168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1223680 : Path.checkChunk context decode facts instructions 1223680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1224192 : Path.checkChunk context decode facts instructions 1224192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1224704 : Path.checkChunk context decode facts instructions 1224704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1225216 : Path.checkChunk context decode facts instructions 1225216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1225728 : Path.checkChunk context decode facts instructions 1225728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1226240 : Path.checkChunk context decode facts instructions 1226240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1226752 : Path.checkChunk context decode facts instructions 1226752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1227264 : Path.checkChunk context decode facts instructions 1227264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1227776 : Path.checkChunk context decode facts instructions 1227776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1228288 : Path.checkChunk context decode facts instructions 1228288 512 = true := by
  decide +kernel

theorem sound_1220608 (prior : ∀ n, n < 1220608 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1228800 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1221120 := Path.chunk_sound context_valid decode facts instructions 1220608 512
    prior checked_1220608
  have h1221632 := Path.chunk_sound context_valid decode facts instructions 1221120 512
    h1221120 checked_1221120
  have h1222144 := Path.chunk_sound context_valid decode facts instructions 1221632 512
    h1221632 checked_1221632
  have h1222656 := Path.chunk_sound context_valid decode facts instructions 1222144 512
    h1222144 checked_1222144
  have h1223168 := Path.chunk_sound context_valid decode facts instructions 1222656 512
    h1222656 checked_1222656
  have h1223680 := Path.chunk_sound context_valid decode facts instructions 1223168 512
    h1223168 checked_1223168
  have h1224192 := Path.chunk_sound context_valid decode facts instructions 1223680 512
    h1223680 checked_1223680
  have h1224704 := Path.chunk_sound context_valid decode facts instructions 1224192 512
    h1224192 checked_1224192
  have h1225216 := Path.chunk_sound context_valid decode facts instructions 1224704 512
    h1224704 checked_1224704
  have h1225728 := Path.chunk_sound context_valid decode facts instructions 1225216 512
    h1225216 checked_1225216
  have h1226240 := Path.chunk_sound context_valid decode facts instructions 1225728 512
    h1225728 checked_1225728
  have h1226752 := Path.chunk_sound context_valid decode facts instructions 1226240 512
    h1226240 checked_1226240
  have h1227264 := Path.chunk_sound context_valid decode facts instructions 1226752 512
    h1226752 checked_1226752
  have h1227776 := Path.chunk_sound context_valid decode facts instructions 1227264 512
    h1227264 checked_1227264
  have h1228288 := Path.chunk_sound context_valid decode facts instructions 1227776 512
    h1227776 checked_1227776
  have h1228800 := Path.chunk_sound context_valid decode facts instructions 1228288 512
    h1228288 checked_1228288
  exact h1228800

end Sporadic.Janko3.AmalgamPresentation.Cover
