module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_909312 : Path.checkChunk context decode facts instructions 909312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_909824 : Path.checkChunk context decode facts instructions 909824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_910336 : Path.checkChunk context decode facts instructions 910336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_910848 : Path.checkChunk context decode facts instructions 910848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_911360 : Path.checkChunk context decode facts instructions 911360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_911872 : Path.checkChunk context decode facts instructions 911872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_912384 : Path.checkChunk context decode facts instructions 912384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_912896 : Path.checkChunk context decode facts instructions 912896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_913408 : Path.checkChunk context decode facts instructions 913408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_913920 : Path.checkChunk context decode facts instructions 913920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_914432 : Path.checkChunk context decode facts instructions 914432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_914944 : Path.checkChunk context decode facts instructions 914944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_915456 : Path.checkChunk context decode facts instructions 915456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_915968 : Path.checkChunk context decode facts instructions 915968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_916480 : Path.checkChunk context decode facts instructions 916480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_916992 : Path.checkChunk context decode facts instructions 916992 512 = true := by
  decide +kernel

theorem sound_909312 (prior : ∀ n, n < 909312 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 917504 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h909824 := Path.chunk_sound context_valid decode facts instructions 909312 512
    prior checked_909312
  have h910336 := Path.chunk_sound context_valid decode facts instructions 909824 512
    h909824 checked_909824
  have h910848 := Path.chunk_sound context_valid decode facts instructions 910336 512
    h910336 checked_910336
  have h911360 := Path.chunk_sound context_valid decode facts instructions 910848 512
    h910848 checked_910848
  have h911872 := Path.chunk_sound context_valid decode facts instructions 911360 512
    h911360 checked_911360
  have h912384 := Path.chunk_sound context_valid decode facts instructions 911872 512
    h911872 checked_911872
  have h912896 := Path.chunk_sound context_valid decode facts instructions 912384 512
    h912384 checked_912384
  have h913408 := Path.chunk_sound context_valid decode facts instructions 912896 512
    h912896 checked_912896
  have h913920 := Path.chunk_sound context_valid decode facts instructions 913408 512
    h913408 checked_913408
  have h914432 := Path.chunk_sound context_valid decode facts instructions 913920 512
    h913920 checked_913920
  have h914944 := Path.chunk_sound context_valid decode facts instructions 914432 512
    h914432 checked_914432
  have h915456 := Path.chunk_sound context_valid decode facts instructions 914944 512
    h914944 checked_914944
  have h915968 := Path.chunk_sound context_valid decode facts instructions 915456 512
    h915456 checked_915456
  have h916480 := Path.chunk_sound context_valid decode facts instructions 915968 512
    h915968 checked_915968
  have h916992 := Path.chunk_sound context_valid decode facts instructions 916480 512
    h916480 checked_916480
  have h917504 := Path.chunk_sound context_valid decode facts instructions 916992 512
    h916992 checked_916992
  exact h917504

end Sporadic.Janko3.AmalgamPresentation.Cover
