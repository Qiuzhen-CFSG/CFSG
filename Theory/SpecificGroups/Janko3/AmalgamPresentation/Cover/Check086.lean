module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_704512 : Path.checkChunk context decode facts instructions 704512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_705024 : Path.checkChunk context decode facts instructions 705024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_705536 : Path.checkChunk context decode facts instructions 705536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_706048 : Path.checkChunk context decode facts instructions 706048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_706560 : Path.checkChunk context decode facts instructions 706560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_707072 : Path.checkChunk context decode facts instructions 707072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_707584 : Path.checkChunk context decode facts instructions 707584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_708096 : Path.checkChunk context decode facts instructions 708096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_708608 : Path.checkChunk context decode facts instructions 708608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_709120 : Path.checkChunk context decode facts instructions 709120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_709632 : Path.checkChunk context decode facts instructions 709632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_710144 : Path.checkChunk context decode facts instructions 710144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_710656 : Path.checkChunk context decode facts instructions 710656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_711168 : Path.checkChunk context decode facts instructions 711168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_711680 : Path.checkChunk context decode facts instructions 711680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_712192 : Path.checkChunk context decode facts instructions 712192 512 = true := by
  decide +kernel

theorem sound_704512 (prior : ∀ n, n < 704512 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 712704 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h705024 := Path.chunk_sound context_valid decode facts instructions 704512 512
    prior checked_704512
  have h705536 := Path.chunk_sound context_valid decode facts instructions 705024 512
    h705024 checked_705024
  have h706048 := Path.chunk_sound context_valid decode facts instructions 705536 512
    h705536 checked_705536
  have h706560 := Path.chunk_sound context_valid decode facts instructions 706048 512
    h706048 checked_706048
  have h707072 := Path.chunk_sound context_valid decode facts instructions 706560 512
    h706560 checked_706560
  have h707584 := Path.chunk_sound context_valid decode facts instructions 707072 512
    h707072 checked_707072
  have h708096 := Path.chunk_sound context_valid decode facts instructions 707584 512
    h707584 checked_707584
  have h708608 := Path.chunk_sound context_valid decode facts instructions 708096 512
    h708096 checked_708096
  have h709120 := Path.chunk_sound context_valid decode facts instructions 708608 512
    h708608 checked_708608
  have h709632 := Path.chunk_sound context_valid decode facts instructions 709120 512
    h709120 checked_709120
  have h710144 := Path.chunk_sound context_valid decode facts instructions 709632 512
    h709632 checked_709632
  have h710656 := Path.chunk_sound context_valid decode facts instructions 710144 512
    h710144 checked_710144
  have h711168 := Path.chunk_sound context_valid decode facts instructions 710656 512
    h710656 checked_710656
  have h711680 := Path.chunk_sound context_valid decode facts instructions 711168 512
    h711168 checked_711168
  have h712192 := Path.chunk_sound context_valid decode facts instructions 711680 512
    h711680 checked_711680
  have h712704 := Path.chunk_sound context_valid decode facts instructions 712192 512
    h712192 checked_712192
  exact h712704

end Sporadic.Janko3.AmalgamPresentation.Cover
