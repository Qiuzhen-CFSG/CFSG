module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_106496 : Path.checkChunk context decode facts instructions 106496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_107008 : Path.checkChunk context decode facts instructions 107008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_107520 : Path.checkChunk context decode facts instructions 107520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_108032 : Path.checkChunk context decode facts instructions 108032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_108544 : Path.checkChunk context decode facts instructions 108544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_109056 : Path.checkChunk context decode facts instructions 109056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_109568 : Path.checkChunk context decode facts instructions 109568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_110080 : Path.checkChunk context decode facts instructions 110080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_110592 : Path.checkChunk context decode facts instructions 110592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_111104 : Path.checkChunk context decode facts instructions 111104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_111616 : Path.checkChunk context decode facts instructions 111616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_112128 : Path.checkChunk context decode facts instructions 112128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_112640 : Path.checkChunk context decode facts instructions 112640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_113152 : Path.checkChunk context decode facts instructions 113152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_113664 : Path.checkChunk context decode facts instructions 113664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_114176 : Path.checkChunk context decode facts instructions 114176 512 = true := by
  decide +kernel

theorem sound_106496 (prior : ∀ n, n < 106496 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 114688 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h107008 := Path.chunk_sound context_valid decode facts instructions 106496 512
    prior checked_106496
  have h107520 := Path.chunk_sound context_valid decode facts instructions 107008 512
    h107008 checked_107008
  have h108032 := Path.chunk_sound context_valid decode facts instructions 107520 512
    h107520 checked_107520
  have h108544 := Path.chunk_sound context_valid decode facts instructions 108032 512
    h108032 checked_108032
  have h109056 := Path.chunk_sound context_valid decode facts instructions 108544 512
    h108544 checked_108544
  have h109568 := Path.chunk_sound context_valid decode facts instructions 109056 512
    h109056 checked_109056
  have h110080 := Path.chunk_sound context_valid decode facts instructions 109568 512
    h109568 checked_109568
  have h110592 := Path.chunk_sound context_valid decode facts instructions 110080 512
    h110080 checked_110080
  have h111104 := Path.chunk_sound context_valid decode facts instructions 110592 512
    h110592 checked_110592
  have h111616 := Path.chunk_sound context_valid decode facts instructions 111104 512
    h111104 checked_111104
  have h112128 := Path.chunk_sound context_valid decode facts instructions 111616 512
    h111616 checked_111616
  have h112640 := Path.chunk_sound context_valid decode facts instructions 112128 512
    h112128 checked_112128
  have h113152 := Path.chunk_sound context_valid decode facts instructions 112640 512
    h112640 checked_112640
  have h113664 := Path.chunk_sound context_valid decode facts instructions 113152 512
    h113152 checked_113152
  have h114176 := Path.chunk_sound context_valid decode facts instructions 113664 512
    h113664 checked_113664
  have h114688 := Path.chunk_sound context_valid decode facts instructions 114176 512
    h114176 checked_114176
  exact h114688

end Sporadic.Janko3.AmalgamPresentation.Cover
