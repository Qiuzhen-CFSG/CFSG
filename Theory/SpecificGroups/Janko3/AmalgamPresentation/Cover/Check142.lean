module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1163264 : Path.checkChunk context decode facts instructions 1163264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1163776 : Path.checkChunk context decode facts instructions 1163776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1164288 : Path.checkChunk context decode facts instructions 1164288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1164800 : Path.checkChunk context decode facts instructions 1164800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1165312 : Path.checkChunk context decode facts instructions 1165312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1165824 : Path.checkChunk context decode facts instructions 1165824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1166336 : Path.checkChunk context decode facts instructions 1166336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1166848 : Path.checkChunk context decode facts instructions 1166848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1167360 : Path.checkChunk context decode facts instructions 1167360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1167872 : Path.checkChunk context decode facts instructions 1167872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1168384 : Path.checkChunk context decode facts instructions 1168384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1168896 : Path.checkChunk context decode facts instructions 1168896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1169408 : Path.checkChunk context decode facts instructions 1169408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1169920 : Path.checkChunk context decode facts instructions 1169920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1170432 : Path.checkChunk context decode facts instructions 1170432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1170944 : Path.checkChunk context decode facts instructions 1170944 512 = true := by
  decide +kernel

theorem sound_1163264 (prior : ∀ n, n < 1163264 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1171456 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1163776 := Path.chunk_sound context_valid decode facts instructions 1163264 512
    prior checked_1163264
  have h1164288 := Path.chunk_sound context_valid decode facts instructions 1163776 512
    h1163776 checked_1163776
  have h1164800 := Path.chunk_sound context_valid decode facts instructions 1164288 512
    h1164288 checked_1164288
  have h1165312 := Path.chunk_sound context_valid decode facts instructions 1164800 512
    h1164800 checked_1164800
  have h1165824 := Path.chunk_sound context_valid decode facts instructions 1165312 512
    h1165312 checked_1165312
  have h1166336 := Path.chunk_sound context_valid decode facts instructions 1165824 512
    h1165824 checked_1165824
  have h1166848 := Path.chunk_sound context_valid decode facts instructions 1166336 512
    h1166336 checked_1166336
  have h1167360 := Path.chunk_sound context_valid decode facts instructions 1166848 512
    h1166848 checked_1166848
  have h1167872 := Path.chunk_sound context_valid decode facts instructions 1167360 512
    h1167360 checked_1167360
  have h1168384 := Path.chunk_sound context_valid decode facts instructions 1167872 512
    h1167872 checked_1167872
  have h1168896 := Path.chunk_sound context_valid decode facts instructions 1168384 512
    h1168384 checked_1168384
  have h1169408 := Path.chunk_sound context_valid decode facts instructions 1168896 512
    h1168896 checked_1168896
  have h1169920 := Path.chunk_sound context_valid decode facts instructions 1169408 512
    h1169408 checked_1169408
  have h1170432 := Path.chunk_sound context_valid decode facts instructions 1169920 512
    h1169920 checked_1169920
  have h1170944 := Path.chunk_sound context_valid decode facts instructions 1170432 512
    h1170432 checked_1170432
  have h1171456 := Path.chunk_sound context_valid decode facts instructions 1170944 512
    h1170944 checked_1170944
  exact h1171456

end Sporadic.Janko3.AmalgamPresentation.Cover
