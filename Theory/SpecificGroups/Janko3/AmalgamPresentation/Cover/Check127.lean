module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1040384 : Path.checkChunk context decode facts instructions 1040384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1040896 : Path.checkChunk context decode facts instructions 1040896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1041408 : Path.checkChunk context decode facts instructions 1041408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1041920 : Path.checkChunk context decode facts instructions 1041920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1042432 : Path.checkChunk context decode facts instructions 1042432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1042944 : Path.checkChunk context decode facts instructions 1042944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1043456 : Path.checkChunk context decode facts instructions 1043456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1043968 : Path.checkChunk context decode facts instructions 1043968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1044480 : Path.checkChunk context decode facts instructions 1044480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1044992 : Path.checkChunk context decode facts instructions 1044992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1045504 : Path.checkChunk context decode facts instructions 1045504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1046016 : Path.checkChunk context decode facts instructions 1046016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1046528 : Path.checkChunk context decode facts instructions 1046528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1047040 : Path.checkChunk context decode facts instructions 1047040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1047552 : Path.checkChunk context decode facts instructions 1047552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1048064 : Path.checkChunk context decode facts instructions 1048064 512 = true := by
  decide +kernel

theorem sound_1040384 (prior : ∀ n, n < 1040384 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1048576 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1040896 := Path.chunk_sound context_valid decode facts instructions 1040384 512
    prior checked_1040384
  have h1041408 := Path.chunk_sound context_valid decode facts instructions 1040896 512
    h1040896 checked_1040896
  have h1041920 := Path.chunk_sound context_valid decode facts instructions 1041408 512
    h1041408 checked_1041408
  have h1042432 := Path.chunk_sound context_valid decode facts instructions 1041920 512
    h1041920 checked_1041920
  have h1042944 := Path.chunk_sound context_valid decode facts instructions 1042432 512
    h1042432 checked_1042432
  have h1043456 := Path.chunk_sound context_valid decode facts instructions 1042944 512
    h1042944 checked_1042944
  have h1043968 := Path.chunk_sound context_valid decode facts instructions 1043456 512
    h1043456 checked_1043456
  have h1044480 := Path.chunk_sound context_valid decode facts instructions 1043968 512
    h1043968 checked_1043968
  have h1044992 := Path.chunk_sound context_valid decode facts instructions 1044480 512
    h1044480 checked_1044480
  have h1045504 := Path.chunk_sound context_valid decode facts instructions 1044992 512
    h1044992 checked_1044992
  have h1046016 := Path.chunk_sound context_valid decode facts instructions 1045504 512
    h1045504 checked_1045504
  have h1046528 := Path.chunk_sound context_valid decode facts instructions 1046016 512
    h1046016 checked_1046016
  have h1047040 := Path.chunk_sound context_valid decode facts instructions 1046528 512
    h1046528 checked_1046528
  have h1047552 := Path.chunk_sound context_valid decode facts instructions 1047040 512
    h1047040 checked_1047040
  have h1048064 := Path.chunk_sound context_valid decode facts instructions 1047552 512
    h1047552 checked_1047552
  have h1048576 := Path.chunk_sound context_valid decode facts instructions 1048064 512
    h1048064 checked_1048064
  exact h1048576

end Sporadic.Janko3.AmalgamPresentation.Cover
