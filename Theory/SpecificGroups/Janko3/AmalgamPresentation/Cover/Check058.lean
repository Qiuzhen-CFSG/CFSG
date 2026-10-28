module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_475136 : Path.checkChunk context decode facts instructions 475136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_475648 : Path.checkChunk context decode facts instructions 475648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_476160 : Path.checkChunk context decode facts instructions 476160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_476672 : Path.checkChunk context decode facts instructions 476672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_477184 : Path.checkChunk context decode facts instructions 477184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_477696 : Path.checkChunk context decode facts instructions 477696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_478208 : Path.checkChunk context decode facts instructions 478208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_478720 : Path.checkChunk context decode facts instructions 478720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_479232 : Path.checkChunk context decode facts instructions 479232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_479744 : Path.checkChunk context decode facts instructions 479744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_480256 : Path.checkChunk context decode facts instructions 480256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_480768 : Path.checkChunk context decode facts instructions 480768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_481280 : Path.checkChunk context decode facts instructions 481280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_481792 : Path.checkChunk context decode facts instructions 481792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_482304 : Path.checkChunk context decode facts instructions 482304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_482816 : Path.checkChunk context decode facts instructions 482816 512 = true := by
  decide +kernel

theorem sound_475136 (prior : ∀ n, n < 475136 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 483328 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h475648 := Path.chunk_sound context_valid decode facts instructions 475136 512
    prior checked_475136
  have h476160 := Path.chunk_sound context_valid decode facts instructions 475648 512
    h475648 checked_475648
  have h476672 := Path.chunk_sound context_valid decode facts instructions 476160 512
    h476160 checked_476160
  have h477184 := Path.chunk_sound context_valid decode facts instructions 476672 512
    h476672 checked_476672
  have h477696 := Path.chunk_sound context_valid decode facts instructions 477184 512
    h477184 checked_477184
  have h478208 := Path.chunk_sound context_valid decode facts instructions 477696 512
    h477696 checked_477696
  have h478720 := Path.chunk_sound context_valid decode facts instructions 478208 512
    h478208 checked_478208
  have h479232 := Path.chunk_sound context_valid decode facts instructions 478720 512
    h478720 checked_478720
  have h479744 := Path.chunk_sound context_valid decode facts instructions 479232 512
    h479232 checked_479232
  have h480256 := Path.chunk_sound context_valid decode facts instructions 479744 512
    h479744 checked_479744
  have h480768 := Path.chunk_sound context_valid decode facts instructions 480256 512
    h480256 checked_480256
  have h481280 := Path.chunk_sound context_valid decode facts instructions 480768 512
    h480768 checked_480768
  have h481792 := Path.chunk_sound context_valid decode facts instructions 481280 512
    h481280 checked_481280
  have h482304 := Path.chunk_sound context_valid decode facts instructions 481792 512
    h481792 checked_481792
  have h482816 := Path.chunk_sound context_valid decode facts instructions 482304 512
    h482304 checked_482304
  have h483328 := Path.chunk_sound context_valid decode facts instructions 482816 512
    h482816 checked_482816
  exact h483328

end Sporadic.Janko3.AmalgamPresentation.Cover
