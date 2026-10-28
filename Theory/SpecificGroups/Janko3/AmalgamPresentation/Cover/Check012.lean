module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_98304 : Path.checkChunk context decode facts instructions 98304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_98816 : Path.checkChunk context decode facts instructions 98816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_99328 : Path.checkChunk context decode facts instructions 99328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_99840 : Path.checkChunk context decode facts instructions 99840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_100352 : Path.checkChunk context decode facts instructions 100352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_100864 : Path.checkChunk context decode facts instructions 100864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_101376 : Path.checkChunk context decode facts instructions 101376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_101888 : Path.checkChunk context decode facts instructions 101888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_102400 : Path.checkChunk context decode facts instructions 102400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_102912 : Path.checkChunk context decode facts instructions 102912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_103424 : Path.checkChunk context decode facts instructions 103424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_103936 : Path.checkChunk context decode facts instructions 103936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_104448 : Path.checkChunk context decode facts instructions 104448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_104960 : Path.checkChunk context decode facts instructions 104960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_105472 : Path.checkChunk context decode facts instructions 105472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_105984 : Path.checkChunk context decode facts instructions 105984 512 = true := by
  decide +kernel

theorem sound_98304 (prior : ∀ n, n < 98304 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 106496 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h98816 := Path.chunk_sound context_valid decode facts instructions 98304 512
    prior checked_98304
  have h99328 := Path.chunk_sound context_valid decode facts instructions 98816 512
    h98816 checked_98816
  have h99840 := Path.chunk_sound context_valid decode facts instructions 99328 512
    h99328 checked_99328
  have h100352 := Path.chunk_sound context_valid decode facts instructions 99840 512
    h99840 checked_99840
  have h100864 := Path.chunk_sound context_valid decode facts instructions 100352 512
    h100352 checked_100352
  have h101376 := Path.chunk_sound context_valid decode facts instructions 100864 512
    h100864 checked_100864
  have h101888 := Path.chunk_sound context_valid decode facts instructions 101376 512
    h101376 checked_101376
  have h102400 := Path.chunk_sound context_valid decode facts instructions 101888 512
    h101888 checked_101888
  have h102912 := Path.chunk_sound context_valid decode facts instructions 102400 512
    h102400 checked_102400
  have h103424 := Path.chunk_sound context_valid decode facts instructions 102912 512
    h102912 checked_102912
  have h103936 := Path.chunk_sound context_valid decode facts instructions 103424 512
    h103424 checked_103424
  have h104448 := Path.chunk_sound context_valid decode facts instructions 103936 512
    h103936 checked_103936
  have h104960 := Path.chunk_sound context_valid decode facts instructions 104448 512
    h104448 checked_104448
  have h105472 := Path.chunk_sound context_valid decode facts instructions 104960 512
    h104960 checked_104960
  have h105984 := Path.chunk_sound context_valid decode facts instructions 105472 512
    h105472 checked_105472
  have h106496 := Path.chunk_sound context_valid decode facts instructions 105984 512
    h105984 checked_105984
  exact h106496

end Sporadic.Janko3.AmalgamPresentation.Cover
