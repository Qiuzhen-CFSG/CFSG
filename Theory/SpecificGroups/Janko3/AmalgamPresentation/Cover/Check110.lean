module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_901120 : Path.checkChunk context decode facts instructions 901120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_901632 : Path.checkChunk context decode facts instructions 901632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_902144 : Path.checkChunk context decode facts instructions 902144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_902656 : Path.checkChunk context decode facts instructions 902656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_903168 : Path.checkChunk context decode facts instructions 903168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_903680 : Path.checkChunk context decode facts instructions 903680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_904192 : Path.checkChunk context decode facts instructions 904192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_904704 : Path.checkChunk context decode facts instructions 904704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_905216 : Path.checkChunk context decode facts instructions 905216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_905728 : Path.checkChunk context decode facts instructions 905728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_906240 : Path.checkChunk context decode facts instructions 906240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_906752 : Path.checkChunk context decode facts instructions 906752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_907264 : Path.checkChunk context decode facts instructions 907264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_907776 : Path.checkChunk context decode facts instructions 907776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_908288 : Path.checkChunk context decode facts instructions 908288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_908800 : Path.checkChunk context decode facts instructions 908800 512 = true := by
  decide +kernel

theorem sound_901120 (prior : ∀ n, n < 901120 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 909312 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h901632 := Path.chunk_sound context_valid decode facts instructions 901120 512
    prior checked_901120
  have h902144 := Path.chunk_sound context_valid decode facts instructions 901632 512
    h901632 checked_901632
  have h902656 := Path.chunk_sound context_valid decode facts instructions 902144 512
    h902144 checked_902144
  have h903168 := Path.chunk_sound context_valid decode facts instructions 902656 512
    h902656 checked_902656
  have h903680 := Path.chunk_sound context_valid decode facts instructions 903168 512
    h903168 checked_903168
  have h904192 := Path.chunk_sound context_valid decode facts instructions 903680 512
    h903680 checked_903680
  have h904704 := Path.chunk_sound context_valid decode facts instructions 904192 512
    h904192 checked_904192
  have h905216 := Path.chunk_sound context_valid decode facts instructions 904704 512
    h904704 checked_904704
  have h905728 := Path.chunk_sound context_valid decode facts instructions 905216 512
    h905216 checked_905216
  have h906240 := Path.chunk_sound context_valid decode facts instructions 905728 512
    h905728 checked_905728
  have h906752 := Path.chunk_sound context_valid decode facts instructions 906240 512
    h906240 checked_906240
  have h907264 := Path.chunk_sound context_valid decode facts instructions 906752 512
    h906752 checked_906752
  have h907776 := Path.chunk_sound context_valid decode facts instructions 907264 512
    h907264 checked_907264
  have h908288 := Path.chunk_sound context_valid decode facts instructions 907776 512
    h907776 checked_907776
  have h908800 := Path.chunk_sound context_valid decode facts instructions 908288 512
    h908288 checked_908288
  have h909312 := Path.chunk_sound context_valid decode facts instructions 908800 512
    h908800 checked_908800
  exact h909312

end Sporadic.Janko3.AmalgamPresentation.Cover
