module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_729088 : Path.checkChunk context decode facts instructions 729088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_729600 : Path.checkChunk context decode facts instructions 729600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_730112 : Path.checkChunk context decode facts instructions 730112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_730624 : Path.checkChunk context decode facts instructions 730624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_731136 : Path.checkChunk context decode facts instructions 731136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_731648 : Path.checkChunk context decode facts instructions 731648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_732160 : Path.checkChunk context decode facts instructions 732160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_732672 : Path.checkChunk context decode facts instructions 732672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_733184 : Path.checkChunk context decode facts instructions 733184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_733696 : Path.checkChunk context decode facts instructions 733696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_734208 : Path.checkChunk context decode facts instructions 734208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_734720 : Path.checkChunk context decode facts instructions 734720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_735232 : Path.checkChunk context decode facts instructions 735232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_735744 : Path.checkChunk context decode facts instructions 735744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_736256 : Path.checkChunk context decode facts instructions 736256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_736768 : Path.checkChunk context decode facts instructions 736768 512 = true := by
  decide +kernel

theorem sound_729088 (prior : ∀ n, n < 729088 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 737280 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h729600 := Path.chunk_sound context_valid decode facts instructions 729088 512
    prior checked_729088
  have h730112 := Path.chunk_sound context_valid decode facts instructions 729600 512
    h729600 checked_729600
  have h730624 := Path.chunk_sound context_valid decode facts instructions 730112 512
    h730112 checked_730112
  have h731136 := Path.chunk_sound context_valid decode facts instructions 730624 512
    h730624 checked_730624
  have h731648 := Path.chunk_sound context_valid decode facts instructions 731136 512
    h731136 checked_731136
  have h732160 := Path.chunk_sound context_valid decode facts instructions 731648 512
    h731648 checked_731648
  have h732672 := Path.chunk_sound context_valid decode facts instructions 732160 512
    h732160 checked_732160
  have h733184 := Path.chunk_sound context_valid decode facts instructions 732672 512
    h732672 checked_732672
  have h733696 := Path.chunk_sound context_valid decode facts instructions 733184 512
    h733184 checked_733184
  have h734208 := Path.chunk_sound context_valid decode facts instructions 733696 512
    h733696 checked_733696
  have h734720 := Path.chunk_sound context_valid decode facts instructions 734208 512
    h734208 checked_734208
  have h735232 := Path.chunk_sound context_valid decode facts instructions 734720 512
    h734720 checked_734720
  have h735744 := Path.chunk_sound context_valid decode facts instructions 735232 512
    h735232 checked_735232
  have h736256 := Path.chunk_sound context_valid decode facts instructions 735744 512
    h735744 checked_735744
  have h736768 := Path.chunk_sound context_valid decode facts instructions 736256 512
    h736256 checked_736256
  have h737280 := Path.chunk_sound context_valid decode facts instructions 736768 512
    h736768 checked_736768
  exact h737280

end Sporadic.Janko3.AmalgamPresentation.Cover
