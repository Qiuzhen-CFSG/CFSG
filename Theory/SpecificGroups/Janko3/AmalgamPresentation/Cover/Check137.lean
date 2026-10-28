module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1122304 : Path.checkChunk context decode facts instructions 1122304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1122816 : Path.checkChunk context decode facts instructions 1122816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1123328 : Path.checkChunk context decode facts instructions 1123328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1123840 : Path.checkChunk context decode facts instructions 1123840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1124352 : Path.checkChunk context decode facts instructions 1124352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1124864 : Path.checkChunk context decode facts instructions 1124864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1125376 : Path.checkChunk context decode facts instructions 1125376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1125888 : Path.checkChunk context decode facts instructions 1125888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1126400 : Path.checkChunk context decode facts instructions 1126400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1126912 : Path.checkChunk context decode facts instructions 1126912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1127424 : Path.checkChunk context decode facts instructions 1127424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1127936 : Path.checkChunk context decode facts instructions 1127936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1128448 : Path.checkChunk context decode facts instructions 1128448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1128960 : Path.checkChunk context decode facts instructions 1128960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1129472 : Path.checkChunk context decode facts instructions 1129472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1129984 : Path.checkChunk context decode facts instructions 1129984 512 = true := by
  decide +kernel

theorem sound_1122304 (prior : ∀ n, n < 1122304 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1130496 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1122816 := Path.chunk_sound context_valid decode facts instructions 1122304 512
    prior checked_1122304
  have h1123328 := Path.chunk_sound context_valid decode facts instructions 1122816 512
    h1122816 checked_1122816
  have h1123840 := Path.chunk_sound context_valid decode facts instructions 1123328 512
    h1123328 checked_1123328
  have h1124352 := Path.chunk_sound context_valid decode facts instructions 1123840 512
    h1123840 checked_1123840
  have h1124864 := Path.chunk_sound context_valid decode facts instructions 1124352 512
    h1124352 checked_1124352
  have h1125376 := Path.chunk_sound context_valid decode facts instructions 1124864 512
    h1124864 checked_1124864
  have h1125888 := Path.chunk_sound context_valid decode facts instructions 1125376 512
    h1125376 checked_1125376
  have h1126400 := Path.chunk_sound context_valid decode facts instructions 1125888 512
    h1125888 checked_1125888
  have h1126912 := Path.chunk_sound context_valid decode facts instructions 1126400 512
    h1126400 checked_1126400
  have h1127424 := Path.chunk_sound context_valid decode facts instructions 1126912 512
    h1126912 checked_1126912
  have h1127936 := Path.chunk_sound context_valid decode facts instructions 1127424 512
    h1127424 checked_1127424
  have h1128448 := Path.chunk_sound context_valid decode facts instructions 1127936 512
    h1127936 checked_1127936
  have h1128960 := Path.chunk_sound context_valid decode facts instructions 1128448 512
    h1128448 checked_1128448
  have h1129472 := Path.chunk_sound context_valid decode facts instructions 1128960 512
    h1128960 checked_1128960
  have h1129984 := Path.chunk_sound context_valid decode facts instructions 1129472 512
    h1129472 checked_1129472
  have h1130496 := Path.chunk_sound context_valid decode facts instructions 1129984 512
    h1129984 checked_1129984
  exact h1130496

end Sporadic.Janko3.AmalgamPresentation.Cover
