module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_434176 : Path.checkChunk context decode facts instructions 434176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_434688 : Path.checkChunk context decode facts instructions 434688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_435200 : Path.checkChunk context decode facts instructions 435200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_435712 : Path.checkChunk context decode facts instructions 435712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_436224 : Path.checkChunk context decode facts instructions 436224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_436736 : Path.checkChunk context decode facts instructions 436736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_437248 : Path.checkChunk context decode facts instructions 437248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_437760 : Path.checkChunk context decode facts instructions 437760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_438272 : Path.checkChunk context decode facts instructions 438272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_438784 : Path.checkChunk context decode facts instructions 438784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_439296 : Path.checkChunk context decode facts instructions 439296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_439808 : Path.checkChunk context decode facts instructions 439808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_440320 : Path.checkChunk context decode facts instructions 440320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_440832 : Path.checkChunk context decode facts instructions 440832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_441344 : Path.checkChunk context decode facts instructions 441344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_441856 : Path.checkChunk context decode facts instructions 441856 512 = true := by
  decide +kernel

theorem sound_434176 (prior : ∀ n, n < 434176 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 442368 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h434688 := Path.chunk_sound context_valid decode facts instructions 434176 512
    prior checked_434176
  have h435200 := Path.chunk_sound context_valid decode facts instructions 434688 512
    h434688 checked_434688
  have h435712 := Path.chunk_sound context_valid decode facts instructions 435200 512
    h435200 checked_435200
  have h436224 := Path.chunk_sound context_valid decode facts instructions 435712 512
    h435712 checked_435712
  have h436736 := Path.chunk_sound context_valid decode facts instructions 436224 512
    h436224 checked_436224
  have h437248 := Path.chunk_sound context_valid decode facts instructions 436736 512
    h436736 checked_436736
  have h437760 := Path.chunk_sound context_valid decode facts instructions 437248 512
    h437248 checked_437248
  have h438272 := Path.chunk_sound context_valid decode facts instructions 437760 512
    h437760 checked_437760
  have h438784 := Path.chunk_sound context_valid decode facts instructions 438272 512
    h438272 checked_438272
  have h439296 := Path.chunk_sound context_valid decode facts instructions 438784 512
    h438784 checked_438784
  have h439808 := Path.chunk_sound context_valid decode facts instructions 439296 512
    h439296 checked_439296
  have h440320 := Path.chunk_sound context_valid decode facts instructions 439808 512
    h439808 checked_439808
  have h440832 := Path.chunk_sound context_valid decode facts instructions 440320 512
    h440320 checked_440320
  have h441344 := Path.chunk_sound context_valid decode facts instructions 440832 512
    h440832 checked_440832
  have h441856 := Path.chunk_sound context_valid decode facts instructions 441344 512
    h441344 checked_441344
  have h442368 := Path.chunk_sound context_valid decode facts instructions 441856 512
    h441856 checked_441856
  exact h442368

end Sporadic.Janko3.AmalgamPresentation.Cover
