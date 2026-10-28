module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_557056 : Path.checkChunk context decode facts instructions 557056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_557568 : Path.checkChunk context decode facts instructions 557568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_558080 : Path.checkChunk context decode facts instructions 558080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_558592 : Path.checkChunk context decode facts instructions 558592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_559104 : Path.checkChunk context decode facts instructions 559104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_559616 : Path.checkChunk context decode facts instructions 559616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_560128 : Path.checkChunk context decode facts instructions 560128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_560640 : Path.checkChunk context decode facts instructions 560640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_561152 : Path.checkChunk context decode facts instructions 561152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_561664 : Path.checkChunk context decode facts instructions 561664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_562176 : Path.checkChunk context decode facts instructions 562176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_562688 : Path.checkChunk context decode facts instructions 562688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_563200 : Path.checkChunk context decode facts instructions 563200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_563712 : Path.checkChunk context decode facts instructions 563712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_564224 : Path.checkChunk context decode facts instructions 564224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_564736 : Path.checkChunk context decode facts instructions 564736 512 = true := by
  decide +kernel

theorem sound_557056 (prior : ∀ n, n < 557056 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 565248 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h557568 := Path.chunk_sound context_valid decode facts instructions 557056 512
    prior checked_557056
  have h558080 := Path.chunk_sound context_valid decode facts instructions 557568 512
    h557568 checked_557568
  have h558592 := Path.chunk_sound context_valid decode facts instructions 558080 512
    h558080 checked_558080
  have h559104 := Path.chunk_sound context_valid decode facts instructions 558592 512
    h558592 checked_558592
  have h559616 := Path.chunk_sound context_valid decode facts instructions 559104 512
    h559104 checked_559104
  have h560128 := Path.chunk_sound context_valid decode facts instructions 559616 512
    h559616 checked_559616
  have h560640 := Path.chunk_sound context_valid decode facts instructions 560128 512
    h560128 checked_560128
  have h561152 := Path.chunk_sound context_valid decode facts instructions 560640 512
    h560640 checked_560640
  have h561664 := Path.chunk_sound context_valid decode facts instructions 561152 512
    h561152 checked_561152
  have h562176 := Path.chunk_sound context_valid decode facts instructions 561664 512
    h561664 checked_561664
  have h562688 := Path.chunk_sound context_valid decode facts instructions 562176 512
    h562176 checked_562176
  have h563200 := Path.chunk_sound context_valid decode facts instructions 562688 512
    h562688 checked_562688
  have h563712 := Path.chunk_sound context_valid decode facts instructions 563200 512
    h563200 checked_563200
  have h564224 := Path.chunk_sound context_valid decode facts instructions 563712 512
    h563712 checked_563712
  have h564736 := Path.chunk_sound context_valid decode facts instructions 564224 512
    h564224 checked_564224
  have h565248 := Path.chunk_sound context_valid decode facts instructions 564736 512
    h564736 checked_564736
  exact h565248

end Sporadic.Janko3.AmalgamPresentation.Cover
