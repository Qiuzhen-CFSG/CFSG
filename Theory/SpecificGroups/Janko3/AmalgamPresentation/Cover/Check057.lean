module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_466944 : Path.checkChunk context decode facts instructions 466944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_467456 : Path.checkChunk context decode facts instructions 467456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_467968 : Path.checkChunk context decode facts instructions 467968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_468480 : Path.checkChunk context decode facts instructions 468480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_468992 : Path.checkChunk context decode facts instructions 468992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_469504 : Path.checkChunk context decode facts instructions 469504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_470016 : Path.checkChunk context decode facts instructions 470016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_470528 : Path.checkChunk context decode facts instructions 470528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_471040 : Path.checkChunk context decode facts instructions 471040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_471552 : Path.checkChunk context decode facts instructions 471552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_472064 : Path.checkChunk context decode facts instructions 472064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_472576 : Path.checkChunk context decode facts instructions 472576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_473088 : Path.checkChunk context decode facts instructions 473088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_473600 : Path.checkChunk context decode facts instructions 473600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_474112 : Path.checkChunk context decode facts instructions 474112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_474624 : Path.checkChunk context decode facts instructions 474624 512 = true := by
  decide +kernel

theorem sound_466944 (prior : ∀ n, n < 466944 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 475136 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h467456 := Path.chunk_sound context_valid decode facts instructions 466944 512
    prior checked_466944
  have h467968 := Path.chunk_sound context_valid decode facts instructions 467456 512
    h467456 checked_467456
  have h468480 := Path.chunk_sound context_valid decode facts instructions 467968 512
    h467968 checked_467968
  have h468992 := Path.chunk_sound context_valid decode facts instructions 468480 512
    h468480 checked_468480
  have h469504 := Path.chunk_sound context_valid decode facts instructions 468992 512
    h468992 checked_468992
  have h470016 := Path.chunk_sound context_valid decode facts instructions 469504 512
    h469504 checked_469504
  have h470528 := Path.chunk_sound context_valid decode facts instructions 470016 512
    h470016 checked_470016
  have h471040 := Path.chunk_sound context_valid decode facts instructions 470528 512
    h470528 checked_470528
  have h471552 := Path.chunk_sound context_valid decode facts instructions 471040 512
    h471040 checked_471040
  have h472064 := Path.chunk_sound context_valid decode facts instructions 471552 512
    h471552 checked_471552
  have h472576 := Path.chunk_sound context_valid decode facts instructions 472064 512
    h472064 checked_472064
  have h473088 := Path.chunk_sound context_valid decode facts instructions 472576 512
    h472576 checked_472576
  have h473600 := Path.chunk_sound context_valid decode facts instructions 473088 512
    h473088 checked_473088
  have h474112 := Path.chunk_sound context_valid decode facts instructions 473600 512
    h473600 checked_473600
  have h474624 := Path.chunk_sound context_valid decode facts instructions 474112 512
    h474112 checked_474112
  have h475136 := Path.chunk_sound context_valid decode facts instructions 474624 512
    h474624 checked_474624
  exact h475136

end Sporadic.Janko3.AmalgamPresentation.Cover
