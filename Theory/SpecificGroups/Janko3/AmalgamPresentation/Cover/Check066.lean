module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_540672 : Path.checkChunk context decode facts instructions 540672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_541184 : Path.checkChunk context decode facts instructions 541184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_541696 : Path.checkChunk context decode facts instructions 541696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_542208 : Path.checkChunk context decode facts instructions 542208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_542720 : Path.checkChunk context decode facts instructions 542720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_543232 : Path.checkChunk context decode facts instructions 543232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_543744 : Path.checkChunk context decode facts instructions 543744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_544256 : Path.checkChunk context decode facts instructions 544256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_544768 : Path.checkChunk context decode facts instructions 544768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_545280 : Path.checkChunk context decode facts instructions 545280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_545792 : Path.checkChunk context decode facts instructions 545792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_546304 : Path.checkChunk context decode facts instructions 546304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_546816 : Path.checkChunk context decode facts instructions 546816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_547328 : Path.checkChunk context decode facts instructions 547328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_547840 : Path.checkChunk context decode facts instructions 547840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_548352 : Path.checkChunk context decode facts instructions 548352 512 = true := by
  decide +kernel

theorem sound_540672 (prior : ∀ n, n < 540672 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 548864 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h541184 := Path.chunk_sound context_valid decode facts instructions 540672 512
    prior checked_540672
  have h541696 := Path.chunk_sound context_valid decode facts instructions 541184 512
    h541184 checked_541184
  have h542208 := Path.chunk_sound context_valid decode facts instructions 541696 512
    h541696 checked_541696
  have h542720 := Path.chunk_sound context_valid decode facts instructions 542208 512
    h542208 checked_542208
  have h543232 := Path.chunk_sound context_valid decode facts instructions 542720 512
    h542720 checked_542720
  have h543744 := Path.chunk_sound context_valid decode facts instructions 543232 512
    h543232 checked_543232
  have h544256 := Path.chunk_sound context_valid decode facts instructions 543744 512
    h543744 checked_543744
  have h544768 := Path.chunk_sound context_valid decode facts instructions 544256 512
    h544256 checked_544256
  have h545280 := Path.chunk_sound context_valid decode facts instructions 544768 512
    h544768 checked_544768
  have h545792 := Path.chunk_sound context_valid decode facts instructions 545280 512
    h545280 checked_545280
  have h546304 := Path.chunk_sound context_valid decode facts instructions 545792 512
    h545792 checked_545792
  have h546816 := Path.chunk_sound context_valid decode facts instructions 546304 512
    h546304 checked_546304
  have h547328 := Path.chunk_sound context_valid decode facts instructions 546816 512
    h546816 checked_546816
  have h547840 := Path.chunk_sound context_valid decode facts instructions 547328 512
    h547328 checked_547328
  have h548352 := Path.chunk_sound context_valid decode facts instructions 547840 512
    h547840 checked_547840
  have h548864 := Path.chunk_sound context_valid decode facts instructions 548352 512
    h548352 checked_548352
  exact h548864

end Sporadic.Janko3.AmalgamPresentation.Cover
