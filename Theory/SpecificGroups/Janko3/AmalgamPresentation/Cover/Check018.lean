module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_147456 : Path.checkChunk context decode facts instructions 147456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_147968 : Path.checkChunk context decode facts instructions 147968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_148480 : Path.checkChunk context decode facts instructions 148480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_148992 : Path.checkChunk context decode facts instructions 148992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_149504 : Path.checkChunk context decode facts instructions 149504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_150016 : Path.checkChunk context decode facts instructions 150016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_150528 : Path.checkChunk context decode facts instructions 150528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_151040 : Path.checkChunk context decode facts instructions 151040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_151552 : Path.checkChunk context decode facts instructions 151552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_152064 : Path.checkChunk context decode facts instructions 152064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_152576 : Path.checkChunk context decode facts instructions 152576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_153088 : Path.checkChunk context decode facts instructions 153088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_153600 : Path.checkChunk context decode facts instructions 153600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_154112 : Path.checkChunk context decode facts instructions 154112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_154624 : Path.checkChunk context decode facts instructions 154624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_155136 : Path.checkChunk context decode facts instructions 155136 512 = true := by
  decide +kernel

theorem sound_147456 (prior : ∀ n, n < 147456 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 155648 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h147968 := Path.chunk_sound context_valid decode facts instructions 147456 512
    prior checked_147456
  have h148480 := Path.chunk_sound context_valid decode facts instructions 147968 512
    h147968 checked_147968
  have h148992 := Path.chunk_sound context_valid decode facts instructions 148480 512
    h148480 checked_148480
  have h149504 := Path.chunk_sound context_valid decode facts instructions 148992 512
    h148992 checked_148992
  have h150016 := Path.chunk_sound context_valid decode facts instructions 149504 512
    h149504 checked_149504
  have h150528 := Path.chunk_sound context_valid decode facts instructions 150016 512
    h150016 checked_150016
  have h151040 := Path.chunk_sound context_valid decode facts instructions 150528 512
    h150528 checked_150528
  have h151552 := Path.chunk_sound context_valid decode facts instructions 151040 512
    h151040 checked_151040
  have h152064 := Path.chunk_sound context_valid decode facts instructions 151552 512
    h151552 checked_151552
  have h152576 := Path.chunk_sound context_valid decode facts instructions 152064 512
    h152064 checked_152064
  have h153088 := Path.chunk_sound context_valid decode facts instructions 152576 512
    h152576 checked_152576
  have h153600 := Path.chunk_sound context_valid decode facts instructions 153088 512
    h153088 checked_153088
  have h154112 := Path.chunk_sound context_valid decode facts instructions 153600 512
    h153600 checked_153600
  have h154624 := Path.chunk_sound context_valid decode facts instructions 154112 512
    h154112 checked_154112
  have h155136 := Path.chunk_sound context_valid decode facts instructions 154624 512
    h154624 checked_154624
  have h155648 := Path.chunk_sound context_valid decode facts instructions 155136 512
    h155136 checked_155136
  exact h155648

end Sporadic.Janko3.AmalgamPresentation.Cover
