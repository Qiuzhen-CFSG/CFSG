module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_327680 : Path.checkChunk context decode facts instructions 327680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_328192 : Path.checkChunk context decode facts instructions 328192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_328704 : Path.checkChunk context decode facts instructions 328704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_329216 : Path.checkChunk context decode facts instructions 329216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_329728 : Path.checkChunk context decode facts instructions 329728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_330240 : Path.checkChunk context decode facts instructions 330240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_330752 : Path.checkChunk context decode facts instructions 330752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_331264 : Path.checkChunk context decode facts instructions 331264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_331776 : Path.checkChunk context decode facts instructions 331776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_332288 : Path.checkChunk context decode facts instructions 332288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_332800 : Path.checkChunk context decode facts instructions 332800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_333312 : Path.checkChunk context decode facts instructions 333312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_333824 : Path.checkChunk context decode facts instructions 333824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_334336 : Path.checkChunk context decode facts instructions 334336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_334848 : Path.checkChunk context decode facts instructions 334848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_335360 : Path.checkChunk context decode facts instructions 335360 512 = true := by
  decide +kernel

theorem sound_327680 (prior : ∀ n, n < 327680 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 335872 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h328192 := Path.chunk_sound context_valid decode facts instructions 327680 512
    prior checked_327680
  have h328704 := Path.chunk_sound context_valid decode facts instructions 328192 512
    h328192 checked_328192
  have h329216 := Path.chunk_sound context_valid decode facts instructions 328704 512
    h328704 checked_328704
  have h329728 := Path.chunk_sound context_valid decode facts instructions 329216 512
    h329216 checked_329216
  have h330240 := Path.chunk_sound context_valid decode facts instructions 329728 512
    h329728 checked_329728
  have h330752 := Path.chunk_sound context_valid decode facts instructions 330240 512
    h330240 checked_330240
  have h331264 := Path.chunk_sound context_valid decode facts instructions 330752 512
    h330752 checked_330752
  have h331776 := Path.chunk_sound context_valid decode facts instructions 331264 512
    h331264 checked_331264
  have h332288 := Path.chunk_sound context_valid decode facts instructions 331776 512
    h331776 checked_331776
  have h332800 := Path.chunk_sound context_valid decode facts instructions 332288 512
    h332288 checked_332288
  have h333312 := Path.chunk_sound context_valid decode facts instructions 332800 512
    h332800 checked_332800
  have h333824 := Path.chunk_sound context_valid decode facts instructions 333312 512
    h333312 checked_333312
  have h334336 := Path.chunk_sound context_valid decode facts instructions 333824 512
    h333824 checked_333824
  have h334848 := Path.chunk_sound context_valid decode facts instructions 334336 512
    h334336 checked_334336
  have h335360 := Path.chunk_sound context_valid decode facts instructions 334848 512
    h334848 checked_334848
  have h335872 := Path.chunk_sound context_valid decode facts instructions 335360 512
    h335360 checked_335360
  exact h335872

end Sporadic.Janko3.AmalgamPresentation.Cover
