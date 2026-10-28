module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1187840 : Path.checkChunk context decode facts instructions 1187840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1188352 : Path.checkChunk context decode facts instructions 1188352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1188864 : Path.checkChunk context decode facts instructions 1188864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1189376 : Path.checkChunk context decode facts instructions 1189376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1189888 : Path.checkChunk context decode facts instructions 1189888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1190400 : Path.checkChunk context decode facts instructions 1190400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1190912 : Path.checkChunk context decode facts instructions 1190912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1191424 : Path.checkChunk context decode facts instructions 1191424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1191936 : Path.checkChunk context decode facts instructions 1191936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1192448 : Path.checkChunk context decode facts instructions 1192448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1192960 : Path.checkChunk context decode facts instructions 1192960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1193472 : Path.checkChunk context decode facts instructions 1193472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1193984 : Path.checkChunk context decode facts instructions 1193984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1194496 : Path.checkChunk context decode facts instructions 1194496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1195008 : Path.checkChunk context decode facts instructions 1195008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1195520 : Path.checkChunk context decode facts instructions 1195520 512 = true := by
  decide +kernel

theorem sound_1187840 (prior : ∀ n, n < 1187840 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1196032 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1188352 := Path.chunk_sound context_valid decode facts instructions 1187840 512
    prior checked_1187840
  have h1188864 := Path.chunk_sound context_valid decode facts instructions 1188352 512
    h1188352 checked_1188352
  have h1189376 := Path.chunk_sound context_valid decode facts instructions 1188864 512
    h1188864 checked_1188864
  have h1189888 := Path.chunk_sound context_valid decode facts instructions 1189376 512
    h1189376 checked_1189376
  have h1190400 := Path.chunk_sound context_valid decode facts instructions 1189888 512
    h1189888 checked_1189888
  have h1190912 := Path.chunk_sound context_valid decode facts instructions 1190400 512
    h1190400 checked_1190400
  have h1191424 := Path.chunk_sound context_valid decode facts instructions 1190912 512
    h1190912 checked_1190912
  have h1191936 := Path.chunk_sound context_valid decode facts instructions 1191424 512
    h1191424 checked_1191424
  have h1192448 := Path.chunk_sound context_valid decode facts instructions 1191936 512
    h1191936 checked_1191936
  have h1192960 := Path.chunk_sound context_valid decode facts instructions 1192448 512
    h1192448 checked_1192448
  have h1193472 := Path.chunk_sound context_valid decode facts instructions 1192960 512
    h1192960 checked_1192960
  have h1193984 := Path.chunk_sound context_valid decode facts instructions 1193472 512
    h1193472 checked_1193472
  have h1194496 := Path.chunk_sound context_valid decode facts instructions 1193984 512
    h1193984 checked_1193984
  have h1195008 := Path.chunk_sound context_valid decode facts instructions 1194496 512
    h1194496 checked_1194496
  have h1195520 := Path.chunk_sound context_valid decode facts instructions 1195008 512
    h1195008 checked_1195008
  have h1196032 := Path.chunk_sound context_valid decode facts instructions 1195520 512
    h1195520 checked_1195520
  exact h1196032

end Sporadic.Janko3.AmalgamPresentation.Cover
