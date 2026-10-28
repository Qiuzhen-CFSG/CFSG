module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1286144 : Path.checkChunk context decode facts instructions 1286144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1286656 : Path.checkChunk context decode facts instructions 1286656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1287168 : Path.checkChunk context decode facts instructions 1287168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1287680 : Path.checkChunk context decode facts instructions 1287680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1288192 : Path.checkChunk context decode facts instructions 1288192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1288704 : Path.checkChunk context decode facts instructions 1288704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1289216 : Path.checkChunk context decode facts instructions 1289216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1289728 : Path.checkChunk context decode facts instructions 1289728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1290240 : Path.checkChunk context decode facts instructions 1290240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1290752 : Path.checkChunk context decode facts instructions 1290752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1291264 : Path.checkChunk context decode facts instructions 1291264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1291776 : Path.checkChunk context decode facts instructions 1291776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1292288 : Path.checkChunk context decode facts instructions 1292288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1292800 : Path.checkChunk context decode facts instructions 1292800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1293312 : Path.checkChunk context decode facts instructions 1293312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1293824 : Path.checkChunk context decode facts instructions 1293824 512 = true := by
  decide +kernel

theorem sound_1286144 (prior : ∀ n, n < 1286144 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1294336 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1286656 := Path.chunk_sound context_valid decode facts instructions 1286144 512
    prior checked_1286144
  have h1287168 := Path.chunk_sound context_valid decode facts instructions 1286656 512
    h1286656 checked_1286656
  have h1287680 := Path.chunk_sound context_valid decode facts instructions 1287168 512
    h1287168 checked_1287168
  have h1288192 := Path.chunk_sound context_valid decode facts instructions 1287680 512
    h1287680 checked_1287680
  have h1288704 := Path.chunk_sound context_valid decode facts instructions 1288192 512
    h1288192 checked_1288192
  have h1289216 := Path.chunk_sound context_valid decode facts instructions 1288704 512
    h1288704 checked_1288704
  have h1289728 := Path.chunk_sound context_valid decode facts instructions 1289216 512
    h1289216 checked_1289216
  have h1290240 := Path.chunk_sound context_valid decode facts instructions 1289728 512
    h1289728 checked_1289728
  have h1290752 := Path.chunk_sound context_valid decode facts instructions 1290240 512
    h1290240 checked_1290240
  have h1291264 := Path.chunk_sound context_valid decode facts instructions 1290752 512
    h1290752 checked_1290752
  have h1291776 := Path.chunk_sound context_valid decode facts instructions 1291264 512
    h1291264 checked_1291264
  have h1292288 := Path.chunk_sound context_valid decode facts instructions 1291776 512
    h1291776 checked_1291776
  have h1292800 := Path.chunk_sound context_valid decode facts instructions 1292288 512
    h1292288 checked_1292288
  have h1293312 := Path.chunk_sound context_valid decode facts instructions 1292800 512
    h1292800 checked_1292800
  have h1293824 := Path.chunk_sound context_valid decode facts instructions 1293312 512
    h1293312 checked_1293312
  have h1294336 := Path.chunk_sound context_valid decode facts instructions 1293824 512
    h1293824 checked_1293824
  exact h1294336

end Sporadic.Janko3.AmalgamPresentation.Cover
