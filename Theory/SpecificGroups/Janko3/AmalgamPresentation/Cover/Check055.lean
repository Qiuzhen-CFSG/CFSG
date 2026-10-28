module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_450560 : Path.checkChunk context decode facts instructions 450560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_451072 : Path.checkChunk context decode facts instructions 451072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_451584 : Path.checkChunk context decode facts instructions 451584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_452096 : Path.checkChunk context decode facts instructions 452096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_452608 : Path.checkChunk context decode facts instructions 452608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_453120 : Path.checkChunk context decode facts instructions 453120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_453632 : Path.checkChunk context decode facts instructions 453632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_454144 : Path.checkChunk context decode facts instructions 454144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_454656 : Path.checkChunk context decode facts instructions 454656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_455168 : Path.checkChunk context decode facts instructions 455168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_455680 : Path.checkChunk context decode facts instructions 455680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_456192 : Path.checkChunk context decode facts instructions 456192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_456704 : Path.checkChunk context decode facts instructions 456704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_457216 : Path.checkChunk context decode facts instructions 457216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_457728 : Path.checkChunk context decode facts instructions 457728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_458240 : Path.checkChunk context decode facts instructions 458240 512 = true := by
  decide +kernel

theorem sound_450560 (prior : ∀ n, n < 450560 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 458752 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h451072 := Path.chunk_sound context_valid decode facts instructions 450560 512
    prior checked_450560
  have h451584 := Path.chunk_sound context_valid decode facts instructions 451072 512
    h451072 checked_451072
  have h452096 := Path.chunk_sound context_valid decode facts instructions 451584 512
    h451584 checked_451584
  have h452608 := Path.chunk_sound context_valid decode facts instructions 452096 512
    h452096 checked_452096
  have h453120 := Path.chunk_sound context_valid decode facts instructions 452608 512
    h452608 checked_452608
  have h453632 := Path.chunk_sound context_valid decode facts instructions 453120 512
    h453120 checked_453120
  have h454144 := Path.chunk_sound context_valid decode facts instructions 453632 512
    h453632 checked_453632
  have h454656 := Path.chunk_sound context_valid decode facts instructions 454144 512
    h454144 checked_454144
  have h455168 := Path.chunk_sound context_valid decode facts instructions 454656 512
    h454656 checked_454656
  have h455680 := Path.chunk_sound context_valid decode facts instructions 455168 512
    h455168 checked_455168
  have h456192 := Path.chunk_sound context_valid decode facts instructions 455680 512
    h455680 checked_455680
  have h456704 := Path.chunk_sound context_valid decode facts instructions 456192 512
    h456192 checked_456192
  have h457216 := Path.chunk_sound context_valid decode facts instructions 456704 512
    h456704 checked_456704
  have h457728 := Path.chunk_sound context_valid decode facts instructions 457216 512
    h457216 checked_457216
  have h458240 := Path.chunk_sound context_valid decode facts instructions 457728 512
    h457728 checked_457728
  have h458752 := Path.chunk_sound context_valid decode facts instructions 458240 512
    h458240 checked_458240
  exact h458752

end Sporadic.Janko3.AmalgamPresentation.Cover
