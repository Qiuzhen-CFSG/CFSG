module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1155072 : Path.checkChunk context decode facts instructions 1155072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1155584 : Path.checkChunk context decode facts instructions 1155584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1156096 : Path.checkChunk context decode facts instructions 1156096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1156608 : Path.checkChunk context decode facts instructions 1156608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1157120 : Path.checkChunk context decode facts instructions 1157120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1157632 : Path.checkChunk context decode facts instructions 1157632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1158144 : Path.checkChunk context decode facts instructions 1158144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1158656 : Path.checkChunk context decode facts instructions 1158656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1159168 : Path.checkChunk context decode facts instructions 1159168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1159680 : Path.checkChunk context decode facts instructions 1159680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1160192 : Path.checkChunk context decode facts instructions 1160192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1160704 : Path.checkChunk context decode facts instructions 1160704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1161216 : Path.checkChunk context decode facts instructions 1161216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1161728 : Path.checkChunk context decode facts instructions 1161728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1162240 : Path.checkChunk context decode facts instructions 1162240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1162752 : Path.checkChunk context decode facts instructions 1162752 512 = true := by
  decide +kernel

theorem sound_1155072 (prior : ∀ n, n < 1155072 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1163264 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1155584 := Path.chunk_sound context_valid decode facts instructions 1155072 512
    prior checked_1155072
  have h1156096 := Path.chunk_sound context_valid decode facts instructions 1155584 512
    h1155584 checked_1155584
  have h1156608 := Path.chunk_sound context_valid decode facts instructions 1156096 512
    h1156096 checked_1156096
  have h1157120 := Path.chunk_sound context_valid decode facts instructions 1156608 512
    h1156608 checked_1156608
  have h1157632 := Path.chunk_sound context_valid decode facts instructions 1157120 512
    h1157120 checked_1157120
  have h1158144 := Path.chunk_sound context_valid decode facts instructions 1157632 512
    h1157632 checked_1157632
  have h1158656 := Path.chunk_sound context_valid decode facts instructions 1158144 512
    h1158144 checked_1158144
  have h1159168 := Path.chunk_sound context_valid decode facts instructions 1158656 512
    h1158656 checked_1158656
  have h1159680 := Path.chunk_sound context_valid decode facts instructions 1159168 512
    h1159168 checked_1159168
  have h1160192 := Path.chunk_sound context_valid decode facts instructions 1159680 512
    h1159680 checked_1159680
  have h1160704 := Path.chunk_sound context_valid decode facts instructions 1160192 512
    h1160192 checked_1160192
  have h1161216 := Path.chunk_sound context_valid decode facts instructions 1160704 512
    h1160704 checked_1160704
  have h1161728 := Path.chunk_sound context_valid decode facts instructions 1161216 512
    h1161216 checked_1161216
  have h1162240 := Path.chunk_sound context_valid decode facts instructions 1161728 512
    h1161728 checked_1161728
  have h1162752 := Path.chunk_sound context_valid decode facts instructions 1162240 512
    h1162240 checked_1162240
  have h1163264 := Path.chunk_sound context_valid decode facts instructions 1162752 512
    h1162752 checked_1162752
  exact h1163264

end Sporadic.Janko3.AmalgamPresentation.Cover
