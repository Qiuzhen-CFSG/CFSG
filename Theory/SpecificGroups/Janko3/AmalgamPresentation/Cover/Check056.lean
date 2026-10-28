module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_458752 : Path.checkChunk context decode facts instructions 458752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_459264 : Path.checkChunk context decode facts instructions 459264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_459776 : Path.checkChunk context decode facts instructions 459776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_460288 : Path.checkChunk context decode facts instructions 460288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_460800 : Path.checkChunk context decode facts instructions 460800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_461312 : Path.checkChunk context decode facts instructions 461312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_461824 : Path.checkChunk context decode facts instructions 461824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_462336 : Path.checkChunk context decode facts instructions 462336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_462848 : Path.checkChunk context decode facts instructions 462848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_463360 : Path.checkChunk context decode facts instructions 463360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_463872 : Path.checkChunk context decode facts instructions 463872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_464384 : Path.checkChunk context decode facts instructions 464384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_464896 : Path.checkChunk context decode facts instructions 464896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_465408 : Path.checkChunk context decode facts instructions 465408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_465920 : Path.checkChunk context decode facts instructions 465920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_466432 : Path.checkChunk context decode facts instructions 466432 512 = true := by
  decide +kernel

theorem sound_458752 (prior : ∀ n, n < 458752 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 466944 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h459264 := Path.chunk_sound context_valid decode facts instructions 458752 512
    prior checked_458752
  have h459776 := Path.chunk_sound context_valid decode facts instructions 459264 512
    h459264 checked_459264
  have h460288 := Path.chunk_sound context_valid decode facts instructions 459776 512
    h459776 checked_459776
  have h460800 := Path.chunk_sound context_valid decode facts instructions 460288 512
    h460288 checked_460288
  have h461312 := Path.chunk_sound context_valid decode facts instructions 460800 512
    h460800 checked_460800
  have h461824 := Path.chunk_sound context_valid decode facts instructions 461312 512
    h461312 checked_461312
  have h462336 := Path.chunk_sound context_valid decode facts instructions 461824 512
    h461824 checked_461824
  have h462848 := Path.chunk_sound context_valid decode facts instructions 462336 512
    h462336 checked_462336
  have h463360 := Path.chunk_sound context_valid decode facts instructions 462848 512
    h462848 checked_462848
  have h463872 := Path.chunk_sound context_valid decode facts instructions 463360 512
    h463360 checked_463360
  have h464384 := Path.chunk_sound context_valid decode facts instructions 463872 512
    h463872 checked_463872
  have h464896 := Path.chunk_sound context_valid decode facts instructions 464384 512
    h464384 checked_464384
  have h465408 := Path.chunk_sound context_valid decode facts instructions 464896 512
    h464896 checked_464896
  have h465920 := Path.chunk_sound context_valid decode facts instructions 465408 512
    h465408 checked_465408
  have h466432 := Path.chunk_sound context_valid decode facts instructions 465920 512
    h465920 checked_465920
  have h466944 := Path.chunk_sound context_valid decode facts instructions 466432 512
    h466432 checked_466432
  exact h466944

end Sporadic.Janko3.AmalgamPresentation.Cover
