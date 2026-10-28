module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_8192 : Path.checkChunk context decode facts instructions 8192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_8704 : Path.checkChunk context decode facts instructions 8704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_9216 : Path.checkChunk context decode facts instructions 9216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_9728 : Path.checkChunk context decode facts instructions 9728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_10240 : Path.checkChunk context decode facts instructions 10240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_10752 : Path.checkChunk context decode facts instructions 10752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_11264 : Path.checkChunk context decode facts instructions 11264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_11776 : Path.checkChunk context decode facts instructions 11776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_12288 : Path.checkChunk context decode facts instructions 12288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_12800 : Path.checkChunk context decode facts instructions 12800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_13312 : Path.checkChunk context decode facts instructions 13312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_13824 : Path.checkChunk context decode facts instructions 13824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_14336 : Path.checkChunk context decode facts instructions 14336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_14848 : Path.checkChunk context decode facts instructions 14848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_15360 : Path.checkChunk context decode facts instructions 15360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_15872 : Path.checkChunk context decode facts instructions 15872 512 = true := by
  decide +kernel

theorem sound_8192 (prior : ∀ n, n < 8192 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 16384 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h8704 := Path.chunk_sound context_valid decode facts instructions 8192 512
    prior checked_8192
  have h9216 := Path.chunk_sound context_valid decode facts instructions 8704 512
    h8704 checked_8704
  have h9728 := Path.chunk_sound context_valid decode facts instructions 9216 512
    h9216 checked_9216
  have h10240 := Path.chunk_sound context_valid decode facts instructions 9728 512
    h9728 checked_9728
  have h10752 := Path.chunk_sound context_valid decode facts instructions 10240 512
    h10240 checked_10240
  have h11264 := Path.chunk_sound context_valid decode facts instructions 10752 512
    h10752 checked_10752
  have h11776 := Path.chunk_sound context_valid decode facts instructions 11264 512
    h11264 checked_11264
  have h12288 := Path.chunk_sound context_valid decode facts instructions 11776 512
    h11776 checked_11776
  have h12800 := Path.chunk_sound context_valid decode facts instructions 12288 512
    h12288 checked_12288
  have h13312 := Path.chunk_sound context_valid decode facts instructions 12800 512
    h12800 checked_12800
  have h13824 := Path.chunk_sound context_valid decode facts instructions 13312 512
    h13312 checked_13312
  have h14336 := Path.chunk_sound context_valid decode facts instructions 13824 512
    h13824 checked_13824
  have h14848 := Path.chunk_sound context_valid decode facts instructions 14336 512
    h14336 checked_14336
  have h15360 := Path.chunk_sound context_valid decode facts instructions 14848 512
    h14848 checked_14848
  have h15872 := Path.chunk_sound context_valid decode facts instructions 15360 512
    h15360 checked_15360
  have h16384 := Path.chunk_sound context_valid decode facts instructions 15872 512
    h15872 checked_15872
  exact h16384

end Sporadic.Janko3.AmalgamPresentation.Cover
