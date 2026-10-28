module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1302528 : Path.checkChunk context decode facts instructions 1302528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1303040 : Path.checkChunk context decode facts instructions 1303040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1303552 : Path.checkChunk context decode facts instructions 1303552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1304064 : Path.checkChunk context decode facts instructions 1304064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1304576 : Path.checkChunk context decode facts instructions 1304576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1305088 : Path.checkChunk context decode facts instructions 1305088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1305600 : Path.checkChunk context decode facts instructions 1305600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1306112 : Path.checkChunk context decode facts instructions 1306112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1306624 : Path.checkChunk context decode facts instructions 1306624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1307136 : Path.checkChunk context decode facts instructions 1307136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1307648 : Path.checkChunk context decode facts instructions 1307648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1308160 : Path.checkChunk context decode facts instructions 1308160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1308672 : Path.checkChunk context decode facts instructions 1308672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1309184 : Path.checkChunk context decode facts instructions 1309184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1309696 : Path.checkChunk context decode facts instructions 1309696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1310208 : Path.checkChunk context decode facts instructions 1310208 512 = true := by
  decide +kernel

theorem sound_1302528 (prior : ∀ n, n < 1302528 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1310720 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1303040 := Path.chunk_sound context_valid decode facts instructions 1302528 512
    prior checked_1302528
  have h1303552 := Path.chunk_sound context_valid decode facts instructions 1303040 512
    h1303040 checked_1303040
  have h1304064 := Path.chunk_sound context_valid decode facts instructions 1303552 512
    h1303552 checked_1303552
  have h1304576 := Path.chunk_sound context_valid decode facts instructions 1304064 512
    h1304064 checked_1304064
  have h1305088 := Path.chunk_sound context_valid decode facts instructions 1304576 512
    h1304576 checked_1304576
  have h1305600 := Path.chunk_sound context_valid decode facts instructions 1305088 512
    h1305088 checked_1305088
  have h1306112 := Path.chunk_sound context_valid decode facts instructions 1305600 512
    h1305600 checked_1305600
  have h1306624 := Path.chunk_sound context_valid decode facts instructions 1306112 512
    h1306112 checked_1306112
  have h1307136 := Path.chunk_sound context_valid decode facts instructions 1306624 512
    h1306624 checked_1306624
  have h1307648 := Path.chunk_sound context_valid decode facts instructions 1307136 512
    h1307136 checked_1307136
  have h1308160 := Path.chunk_sound context_valid decode facts instructions 1307648 512
    h1307648 checked_1307648
  have h1308672 := Path.chunk_sound context_valid decode facts instructions 1308160 512
    h1308160 checked_1308160
  have h1309184 := Path.chunk_sound context_valid decode facts instructions 1308672 512
    h1308672 checked_1308672
  have h1309696 := Path.chunk_sound context_valid decode facts instructions 1309184 512
    h1309184 checked_1309184
  have h1310208 := Path.chunk_sound context_valid decode facts instructions 1309696 512
    h1309696 checked_1309696
  have h1310720 := Path.chunk_sound context_valid decode facts instructions 1310208 512
    h1310208 checked_1310208
  exact h1310720

end Sporadic.Janko3.AmalgamPresentation.Cover
