module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_581632 : Path.checkChunk context decode facts instructions 581632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_582144 : Path.checkChunk context decode facts instructions 582144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_582656 : Path.checkChunk context decode facts instructions 582656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_583168 : Path.checkChunk context decode facts instructions 583168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_583680 : Path.checkChunk context decode facts instructions 583680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_584192 : Path.checkChunk context decode facts instructions 584192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_584704 : Path.checkChunk context decode facts instructions 584704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_585216 : Path.checkChunk context decode facts instructions 585216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_585728 : Path.checkChunk context decode facts instructions 585728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_586240 : Path.checkChunk context decode facts instructions 586240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_586752 : Path.checkChunk context decode facts instructions 586752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_587264 : Path.checkChunk context decode facts instructions 587264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_587776 : Path.checkChunk context decode facts instructions 587776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_588288 : Path.checkChunk context decode facts instructions 588288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_588800 : Path.checkChunk context decode facts instructions 588800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_589312 : Path.checkChunk context decode facts instructions 589312 512 = true := by
  decide +kernel

theorem sound_581632 (prior : ∀ n, n < 581632 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 589824 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h582144 := Path.chunk_sound context_valid decode facts instructions 581632 512
    prior checked_581632
  have h582656 := Path.chunk_sound context_valid decode facts instructions 582144 512
    h582144 checked_582144
  have h583168 := Path.chunk_sound context_valid decode facts instructions 582656 512
    h582656 checked_582656
  have h583680 := Path.chunk_sound context_valid decode facts instructions 583168 512
    h583168 checked_583168
  have h584192 := Path.chunk_sound context_valid decode facts instructions 583680 512
    h583680 checked_583680
  have h584704 := Path.chunk_sound context_valid decode facts instructions 584192 512
    h584192 checked_584192
  have h585216 := Path.chunk_sound context_valid decode facts instructions 584704 512
    h584704 checked_584704
  have h585728 := Path.chunk_sound context_valid decode facts instructions 585216 512
    h585216 checked_585216
  have h586240 := Path.chunk_sound context_valid decode facts instructions 585728 512
    h585728 checked_585728
  have h586752 := Path.chunk_sound context_valid decode facts instructions 586240 512
    h586240 checked_586240
  have h587264 := Path.chunk_sound context_valid decode facts instructions 586752 512
    h586752 checked_586752
  have h587776 := Path.chunk_sound context_valid decode facts instructions 587264 512
    h587264 checked_587264
  have h588288 := Path.chunk_sound context_valid decode facts instructions 587776 512
    h587776 checked_587776
  have h588800 := Path.chunk_sound context_valid decode facts instructions 588288 512
    h588288 checked_588288
  have h589312 := Path.chunk_sound context_valid decode facts instructions 588800 512
    h588800 checked_588800
  have h589824 := Path.chunk_sound context_valid decode facts instructions 589312 512
    h589312 checked_589312
  exact h589824

end Sporadic.Janko3.AmalgamPresentation.Cover
