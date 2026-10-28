module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1474560 : Path.checkChunk context decode facts instructions 1474560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1475072 : Path.checkChunk context decode facts instructions 1475072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1475584 : Path.checkChunk context decode facts instructions 1475584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1476096 : Path.checkChunk context decode facts instructions 1476096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1476608 : Path.checkChunk context decode facts instructions 1476608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1477120 : Path.checkChunk context decode facts instructions 1477120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1477632 : Path.checkChunk context decode facts instructions 1477632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1478144 : Path.checkChunk context decode facts instructions 1478144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1478656 : Path.checkChunk context decode facts instructions 1478656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1479168 : Path.checkChunk context decode facts instructions 1479168 34 = true := by
  decide +kernel

theorem sound_1474560 (prior : ∀ n, n < 1474560 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1479202 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1475072 := Path.chunk_sound context_valid decode facts instructions 1474560 512
    prior checked_1474560
  have h1475584 := Path.chunk_sound context_valid decode facts instructions 1475072 512
    h1475072 checked_1475072
  have h1476096 := Path.chunk_sound context_valid decode facts instructions 1475584 512
    h1475584 checked_1475584
  have h1476608 := Path.chunk_sound context_valid decode facts instructions 1476096 512
    h1476096 checked_1476096
  have h1477120 := Path.chunk_sound context_valid decode facts instructions 1476608 512
    h1476608 checked_1476608
  have h1477632 := Path.chunk_sound context_valid decode facts instructions 1477120 512
    h1477120 checked_1477120
  have h1478144 := Path.chunk_sound context_valid decode facts instructions 1477632 512
    h1477632 checked_1477632
  have h1478656 := Path.chunk_sound context_valid decode facts instructions 1478144 512
    h1478144 checked_1478144
  have h1479168 := Path.chunk_sound context_valid decode facts instructions 1478656 512
    h1478656 checked_1478656
  have h1479202 := Path.chunk_sound context_valid decode facts instructions 1479168 34
    h1479168 checked_1479168
  exact h1479202

end Sporadic.Janko3.AmalgamPresentation.Cover
