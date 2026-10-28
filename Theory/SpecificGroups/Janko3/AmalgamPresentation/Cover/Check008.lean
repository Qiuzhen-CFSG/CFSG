module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_65536 : Path.checkChunk context decode facts instructions 65536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_66048 : Path.checkChunk context decode facts instructions 66048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_66560 : Path.checkChunk context decode facts instructions 66560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_67072 : Path.checkChunk context decode facts instructions 67072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_67584 : Path.checkChunk context decode facts instructions 67584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_68096 : Path.checkChunk context decode facts instructions 68096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_68608 : Path.checkChunk context decode facts instructions 68608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_69120 : Path.checkChunk context decode facts instructions 69120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_69632 : Path.checkChunk context decode facts instructions 69632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_70144 : Path.checkChunk context decode facts instructions 70144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_70656 : Path.checkChunk context decode facts instructions 70656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_71168 : Path.checkChunk context decode facts instructions 71168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_71680 : Path.checkChunk context decode facts instructions 71680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_72192 : Path.checkChunk context decode facts instructions 72192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_72704 : Path.checkChunk context decode facts instructions 72704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_73216 : Path.checkChunk context decode facts instructions 73216 512 = true := by
  decide +kernel

theorem sound_65536 (prior : ∀ n, n < 65536 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 73728 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h66048 := Path.chunk_sound context_valid decode facts instructions 65536 512
    prior checked_65536
  have h66560 := Path.chunk_sound context_valid decode facts instructions 66048 512
    h66048 checked_66048
  have h67072 := Path.chunk_sound context_valid decode facts instructions 66560 512
    h66560 checked_66560
  have h67584 := Path.chunk_sound context_valid decode facts instructions 67072 512
    h67072 checked_67072
  have h68096 := Path.chunk_sound context_valid decode facts instructions 67584 512
    h67584 checked_67584
  have h68608 := Path.chunk_sound context_valid decode facts instructions 68096 512
    h68096 checked_68096
  have h69120 := Path.chunk_sound context_valid decode facts instructions 68608 512
    h68608 checked_68608
  have h69632 := Path.chunk_sound context_valid decode facts instructions 69120 512
    h69120 checked_69120
  have h70144 := Path.chunk_sound context_valid decode facts instructions 69632 512
    h69632 checked_69632
  have h70656 := Path.chunk_sound context_valid decode facts instructions 70144 512
    h70144 checked_70144
  have h71168 := Path.chunk_sound context_valid decode facts instructions 70656 512
    h70656 checked_70656
  have h71680 := Path.chunk_sound context_valid decode facts instructions 71168 512
    h71168 checked_71168
  have h72192 := Path.chunk_sound context_valid decode facts instructions 71680 512
    h71680 checked_71680
  have h72704 := Path.chunk_sound context_valid decode facts instructions 72192 512
    h72192 checked_72192
  have h73216 := Path.chunk_sound context_valid decode facts instructions 72704 512
    h72704 checked_72704
  have h73728 := Path.chunk_sound context_valid decode facts instructions 73216 512
    h73216 checked_73216
  exact h73728

end Sporadic.Janko3.AmalgamPresentation.Cover
