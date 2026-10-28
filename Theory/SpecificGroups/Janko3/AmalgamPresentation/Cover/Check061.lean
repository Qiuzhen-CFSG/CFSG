module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_499712 : Path.checkChunk context decode facts instructions 499712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_500224 : Path.checkChunk context decode facts instructions 500224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_500736 : Path.checkChunk context decode facts instructions 500736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_501248 : Path.checkChunk context decode facts instructions 501248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_501760 : Path.checkChunk context decode facts instructions 501760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_502272 : Path.checkChunk context decode facts instructions 502272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_502784 : Path.checkChunk context decode facts instructions 502784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_503296 : Path.checkChunk context decode facts instructions 503296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_503808 : Path.checkChunk context decode facts instructions 503808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_504320 : Path.checkChunk context decode facts instructions 504320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_504832 : Path.checkChunk context decode facts instructions 504832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_505344 : Path.checkChunk context decode facts instructions 505344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_505856 : Path.checkChunk context decode facts instructions 505856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_506368 : Path.checkChunk context decode facts instructions 506368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_506880 : Path.checkChunk context decode facts instructions 506880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_507392 : Path.checkChunk context decode facts instructions 507392 512 = true := by
  decide +kernel

theorem sound_499712 (prior : ∀ n, n < 499712 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 507904 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h500224 := Path.chunk_sound context_valid decode facts instructions 499712 512
    prior checked_499712
  have h500736 := Path.chunk_sound context_valid decode facts instructions 500224 512
    h500224 checked_500224
  have h501248 := Path.chunk_sound context_valid decode facts instructions 500736 512
    h500736 checked_500736
  have h501760 := Path.chunk_sound context_valid decode facts instructions 501248 512
    h501248 checked_501248
  have h502272 := Path.chunk_sound context_valid decode facts instructions 501760 512
    h501760 checked_501760
  have h502784 := Path.chunk_sound context_valid decode facts instructions 502272 512
    h502272 checked_502272
  have h503296 := Path.chunk_sound context_valid decode facts instructions 502784 512
    h502784 checked_502784
  have h503808 := Path.chunk_sound context_valid decode facts instructions 503296 512
    h503296 checked_503296
  have h504320 := Path.chunk_sound context_valid decode facts instructions 503808 512
    h503808 checked_503808
  have h504832 := Path.chunk_sound context_valid decode facts instructions 504320 512
    h504320 checked_504320
  have h505344 := Path.chunk_sound context_valid decode facts instructions 504832 512
    h504832 checked_504832
  have h505856 := Path.chunk_sound context_valid decode facts instructions 505344 512
    h505344 checked_505344
  have h506368 := Path.chunk_sound context_valid decode facts instructions 505856 512
    h505856 checked_505856
  have h506880 := Path.chunk_sound context_valid decode facts instructions 506368 512
    h506368 checked_506368
  have h507392 := Path.chunk_sound context_valid decode facts instructions 506880 512
    h506880 checked_506880
  have h507904 := Path.chunk_sound context_valid decode facts instructions 507392 512
    h507392 checked_507392
  exact h507904

end Sporadic.Janko3.AmalgamPresentation.Cover
