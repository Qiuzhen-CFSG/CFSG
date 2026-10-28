module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1032192 : Path.checkChunk context decode facts instructions 1032192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1032704 : Path.checkChunk context decode facts instructions 1032704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1033216 : Path.checkChunk context decode facts instructions 1033216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1033728 : Path.checkChunk context decode facts instructions 1033728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1034240 : Path.checkChunk context decode facts instructions 1034240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1034752 : Path.checkChunk context decode facts instructions 1034752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1035264 : Path.checkChunk context decode facts instructions 1035264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1035776 : Path.checkChunk context decode facts instructions 1035776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1036288 : Path.checkChunk context decode facts instructions 1036288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1036800 : Path.checkChunk context decode facts instructions 1036800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1037312 : Path.checkChunk context decode facts instructions 1037312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1037824 : Path.checkChunk context decode facts instructions 1037824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1038336 : Path.checkChunk context decode facts instructions 1038336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1038848 : Path.checkChunk context decode facts instructions 1038848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1039360 : Path.checkChunk context decode facts instructions 1039360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1039872 : Path.checkChunk context decode facts instructions 1039872 512 = true := by
  decide +kernel

theorem sound_1032192 (prior : ∀ n, n < 1032192 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1040384 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1032704 := Path.chunk_sound context_valid decode facts instructions 1032192 512
    prior checked_1032192
  have h1033216 := Path.chunk_sound context_valid decode facts instructions 1032704 512
    h1032704 checked_1032704
  have h1033728 := Path.chunk_sound context_valid decode facts instructions 1033216 512
    h1033216 checked_1033216
  have h1034240 := Path.chunk_sound context_valid decode facts instructions 1033728 512
    h1033728 checked_1033728
  have h1034752 := Path.chunk_sound context_valid decode facts instructions 1034240 512
    h1034240 checked_1034240
  have h1035264 := Path.chunk_sound context_valid decode facts instructions 1034752 512
    h1034752 checked_1034752
  have h1035776 := Path.chunk_sound context_valid decode facts instructions 1035264 512
    h1035264 checked_1035264
  have h1036288 := Path.chunk_sound context_valid decode facts instructions 1035776 512
    h1035776 checked_1035776
  have h1036800 := Path.chunk_sound context_valid decode facts instructions 1036288 512
    h1036288 checked_1036288
  have h1037312 := Path.chunk_sound context_valid decode facts instructions 1036800 512
    h1036800 checked_1036800
  have h1037824 := Path.chunk_sound context_valid decode facts instructions 1037312 512
    h1037312 checked_1037312
  have h1038336 := Path.chunk_sound context_valid decode facts instructions 1037824 512
    h1037824 checked_1037824
  have h1038848 := Path.chunk_sound context_valid decode facts instructions 1038336 512
    h1038336 checked_1038336
  have h1039360 := Path.chunk_sound context_valid decode facts instructions 1038848 512
    h1038848 checked_1038848
  have h1039872 := Path.chunk_sound context_valid decode facts instructions 1039360 512
    h1039360 checked_1039360
  have h1040384 := Path.chunk_sound context_valid decode facts instructions 1039872 512
    h1039872 checked_1039872
  exact h1040384

end Sporadic.Janko3.AmalgamPresentation.Cover
