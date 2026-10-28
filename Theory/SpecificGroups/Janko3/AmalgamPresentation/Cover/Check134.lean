module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1097728 : Path.checkChunk context decode facts instructions 1097728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1098240 : Path.checkChunk context decode facts instructions 1098240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1098752 : Path.checkChunk context decode facts instructions 1098752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1099264 : Path.checkChunk context decode facts instructions 1099264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1099776 : Path.checkChunk context decode facts instructions 1099776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1100288 : Path.checkChunk context decode facts instructions 1100288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1100800 : Path.checkChunk context decode facts instructions 1100800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1101312 : Path.checkChunk context decode facts instructions 1101312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1101824 : Path.checkChunk context decode facts instructions 1101824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1102336 : Path.checkChunk context decode facts instructions 1102336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1102848 : Path.checkChunk context decode facts instructions 1102848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1103360 : Path.checkChunk context decode facts instructions 1103360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1103872 : Path.checkChunk context decode facts instructions 1103872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1104384 : Path.checkChunk context decode facts instructions 1104384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1104896 : Path.checkChunk context decode facts instructions 1104896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1105408 : Path.checkChunk context decode facts instructions 1105408 512 = true := by
  decide +kernel

theorem sound_1097728 (prior : ∀ n, n < 1097728 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1105920 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1098240 := Path.chunk_sound context_valid decode facts instructions 1097728 512
    prior checked_1097728
  have h1098752 := Path.chunk_sound context_valid decode facts instructions 1098240 512
    h1098240 checked_1098240
  have h1099264 := Path.chunk_sound context_valid decode facts instructions 1098752 512
    h1098752 checked_1098752
  have h1099776 := Path.chunk_sound context_valid decode facts instructions 1099264 512
    h1099264 checked_1099264
  have h1100288 := Path.chunk_sound context_valid decode facts instructions 1099776 512
    h1099776 checked_1099776
  have h1100800 := Path.chunk_sound context_valid decode facts instructions 1100288 512
    h1100288 checked_1100288
  have h1101312 := Path.chunk_sound context_valid decode facts instructions 1100800 512
    h1100800 checked_1100800
  have h1101824 := Path.chunk_sound context_valid decode facts instructions 1101312 512
    h1101312 checked_1101312
  have h1102336 := Path.chunk_sound context_valid decode facts instructions 1101824 512
    h1101824 checked_1101824
  have h1102848 := Path.chunk_sound context_valid decode facts instructions 1102336 512
    h1102336 checked_1102336
  have h1103360 := Path.chunk_sound context_valid decode facts instructions 1102848 512
    h1102848 checked_1102848
  have h1103872 := Path.chunk_sound context_valid decode facts instructions 1103360 512
    h1103360 checked_1103360
  have h1104384 := Path.chunk_sound context_valid decode facts instructions 1103872 512
    h1103872 checked_1103872
  have h1104896 := Path.chunk_sound context_valid decode facts instructions 1104384 512
    h1104384 checked_1104384
  have h1105408 := Path.chunk_sound context_valid decode facts instructions 1104896 512
    h1104896 checked_1104896
  have h1105920 := Path.chunk_sound context_valid decode facts instructions 1105408 512
    h1105408 checked_1105408
  exact h1105920

end Sporadic.Janko3.AmalgamPresentation.Cover
