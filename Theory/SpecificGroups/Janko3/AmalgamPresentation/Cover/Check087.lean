module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_712704 : Path.checkChunk context decode facts instructions 712704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_713216 : Path.checkChunk context decode facts instructions 713216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_713728 : Path.checkChunk context decode facts instructions 713728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_714240 : Path.checkChunk context decode facts instructions 714240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_714752 : Path.checkChunk context decode facts instructions 714752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_715264 : Path.checkChunk context decode facts instructions 715264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_715776 : Path.checkChunk context decode facts instructions 715776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_716288 : Path.checkChunk context decode facts instructions 716288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_716800 : Path.checkChunk context decode facts instructions 716800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_717312 : Path.checkChunk context decode facts instructions 717312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_717824 : Path.checkChunk context decode facts instructions 717824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_718336 : Path.checkChunk context decode facts instructions 718336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_718848 : Path.checkChunk context decode facts instructions 718848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_719360 : Path.checkChunk context decode facts instructions 719360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_719872 : Path.checkChunk context decode facts instructions 719872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_720384 : Path.checkChunk context decode facts instructions 720384 512 = true := by
  decide +kernel

theorem sound_712704 (prior : ∀ n, n < 712704 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 720896 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h713216 := Path.chunk_sound context_valid decode facts instructions 712704 512
    prior checked_712704
  have h713728 := Path.chunk_sound context_valid decode facts instructions 713216 512
    h713216 checked_713216
  have h714240 := Path.chunk_sound context_valid decode facts instructions 713728 512
    h713728 checked_713728
  have h714752 := Path.chunk_sound context_valid decode facts instructions 714240 512
    h714240 checked_714240
  have h715264 := Path.chunk_sound context_valid decode facts instructions 714752 512
    h714752 checked_714752
  have h715776 := Path.chunk_sound context_valid decode facts instructions 715264 512
    h715264 checked_715264
  have h716288 := Path.chunk_sound context_valid decode facts instructions 715776 512
    h715776 checked_715776
  have h716800 := Path.chunk_sound context_valid decode facts instructions 716288 512
    h716288 checked_716288
  have h717312 := Path.chunk_sound context_valid decode facts instructions 716800 512
    h716800 checked_716800
  have h717824 := Path.chunk_sound context_valid decode facts instructions 717312 512
    h717312 checked_717312
  have h718336 := Path.chunk_sound context_valid decode facts instructions 717824 512
    h717824 checked_717824
  have h718848 := Path.chunk_sound context_valid decode facts instructions 718336 512
    h718336 checked_718336
  have h719360 := Path.chunk_sound context_valid decode facts instructions 718848 512
    h718848 checked_718848
  have h719872 := Path.chunk_sound context_valid decode facts instructions 719360 512
    h719360 checked_719360
  have h720384 := Path.chunk_sound context_valid decode facts instructions 719872 512
    h719872 checked_719872
  have h720896 := Path.chunk_sound context_valid decode facts instructions 720384 512
    h720384 checked_720384
  exact h720896

end Sporadic.Janko3.AmalgamPresentation.Cover
