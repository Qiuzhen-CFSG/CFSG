module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1105920 : Path.checkChunk context decode facts instructions 1105920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1106432 : Path.checkChunk context decode facts instructions 1106432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1106944 : Path.checkChunk context decode facts instructions 1106944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1107456 : Path.checkChunk context decode facts instructions 1107456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1107968 : Path.checkChunk context decode facts instructions 1107968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1108480 : Path.checkChunk context decode facts instructions 1108480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1108992 : Path.checkChunk context decode facts instructions 1108992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1109504 : Path.checkChunk context decode facts instructions 1109504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1110016 : Path.checkChunk context decode facts instructions 1110016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1110528 : Path.checkChunk context decode facts instructions 1110528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1111040 : Path.checkChunk context decode facts instructions 1111040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1111552 : Path.checkChunk context decode facts instructions 1111552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1112064 : Path.checkChunk context decode facts instructions 1112064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1112576 : Path.checkChunk context decode facts instructions 1112576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1113088 : Path.checkChunk context decode facts instructions 1113088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1113600 : Path.checkChunk context decode facts instructions 1113600 512 = true := by
  decide +kernel

theorem sound_1105920 (prior : ∀ n, n < 1105920 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1114112 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1106432 := Path.chunk_sound context_valid decode facts instructions 1105920 512
    prior checked_1105920
  have h1106944 := Path.chunk_sound context_valid decode facts instructions 1106432 512
    h1106432 checked_1106432
  have h1107456 := Path.chunk_sound context_valid decode facts instructions 1106944 512
    h1106944 checked_1106944
  have h1107968 := Path.chunk_sound context_valid decode facts instructions 1107456 512
    h1107456 checked_1107456
  have h1108480 := Path.chunk_sound context_valid decode facts instructions 1107968 512
    h1107968 checked_1107968
  have h1108992 := Path.chunk_sound context_valid decode facts instructions 1108480 512
    h1108480 checked_1108480
  have h1109504 := Path.chunk_sound context_valid decode facts instructions 1108992 512
    h1108992 checked_1108992
  have h1110016 := Path.chunk_sound context_valid decode facts instructions 1109504 512
    h1109504 checked_1109504
  have h1110528 := Path.chunk_sound context_valid decode facts instructions 1110016 512
    h1110016 checked_1110016
  have h1111040 := Path.chunk_sound context_valid decode facts instructions 1110528 512
    h1110528 checked_1110528
  have h1111552 := Path.chunk_sound context_valid decode facts instructions 1111040 512
    h1111040 checked_1111040
  have h1112064 := Path.chunk_sound context_valid decode facts instructions 1111552 512
    h1111552 checked_1111552
  have h1112576 := Path.chunk_sound context_valid decode facts instructions 1112064 512
    h1112064 checked_1112064
  have h1113088 := Path.chunk_sound context_valid decode facts instructions 1112576 512
    h1112576 checked_1112576
  have h1113600 := Path.chunk_sound context_valid decode facts instructions 1113088 512
    h1113088 checked_1113088
  have h1114112 := Path.chunk_sound context_valid decode facts instructions 1113600 512
    h1113600 checked_1113600
  exact h1114112

end Sporadic.Janko3.AmalgamPresentation.Cover
