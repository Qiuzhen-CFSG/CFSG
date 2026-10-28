module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_548864 : Path.checkChunk context decode facts instructions 548864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_549376 : Path.checkChunk context decode facts instructions 549376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_549888 : Path.checkChunk context decode facts instructions 549888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_550400 : Path.checkChunk context decode facts instructions 550400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_550912 : Path.checkChunk context decode facts instructions 550912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_551424 : Path.checkChunk context decode facts instructions 551424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_551936 : Path.checkChunk context decode facts instructions 551936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_552448 : Path.checkChunk context decode facts instructions 552448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_552960 : Path.checkChunk context decode facts instructions 552960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_553472 : Path.checkChunk context decode facts instructions 553472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_553984 : Path.checkChunk context decode facts instructions 553984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_554496 : Path.checkChunk context decode facts instructions 554496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_555008 : Path.checkChunk context decode facts instructions 555008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_555520 : Path.checkChunk context decode facts instructions 555520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_556032 : Path.checkChunk context decode facts instructions 556032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_556544 : Path.checkChunk context decode facts instructions 556544 512 = true := by
  decide +kernel

theorem sound_548864 (prior : ∀ n, n < 548864 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 557056 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h549376 := Path.chunk_sound context_valid decode facts instructions 548864 512
    prior checked_548864
  have h549888 := Path.chunk_sound context_valid decode facts instructions 549376 512
    h549376 checked_549376
  have h550400 := Path.chunk_sound context_valid decode facts instructions 549888 512
    h549888 checked_549888
  have h550912 := Path.chunk_sound context_valid decode facts instructions 550400 512
    h550400 checked_550400
  have h551424 := Path.chunk_sound context_valid decode facts instructions 550912 512
    h550912 checked_550912
  have h551936 := Path.chunk_sound context_valid decode facts instructions 551424 512
    h551424 checked_551424
  have h552448 := Path.chunk_sound context_valid decode facts instructions 551936 512
    h551936 checked_551936
  have h552960 := Path.chunk_sound context_valid decode facts instructions 552448 512
    h552448 checked_552448
  have h553472 := Path.chunk_sound context_valid decode facts instructions 552960 512
    h552960 checked_552960
  have h553984 := Path.chunk_sound context_valid decode facts instructions 553472 512
    h553472 checked_553472
  have h554496 := Path.chunk_sound context_valid decode facts instructions 553984 512
    h553984 checked_553984
  have h555008 := Path.chunk_sound context_valid decode facts instructions 554496 512
    h554496 checked_554496
  have h555520 := Path.chunk_sound context_valid decode facts instructions 555008 512
    h555008 checked_555008
  have h556032 := Path.chunk_sound context_valid decode facts instructions 555520 512
    h555520 checked_555520
  have h556544 := Path.chunk_sound context_valid decode facts instructions 556032 512
    h556032 checked_556032
  have h557056 := Path.chunk_sound context_valid decode facts instructions 556544 512
    h556544 checked_556544
  exact h557056

end Sporadic.Janko3.AmalgamPresentation.Cover
