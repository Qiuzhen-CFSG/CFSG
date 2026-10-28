module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1114112 : Path.checkChunk context decode facts instructions 1114112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1114624 : Path.checkChunk context decode facts instructions 1114624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1115136 : Path.checkChunk context decode facts instructions 1115136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1115648 : Path.checkChunk context decode facts instructions 1115648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1116160 : Path.checkChunk context decode facts instructions 1116160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1116672 : Path.checkChunk context decode facts instructions 1116672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1117184 : Path.checkChunk context decode facts instructions 1117184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1117696 : Path.checkChunk context decode facts instructions 1117696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1118208 : Path.checkChunk context decode facts instructions 1118208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1118720 : Path.checkChunk context decode facts instructions 1118720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1119232 : Path.checkChunk context decode facts instructions 1119232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1119744 : Path.checkChunk context decode facts instructions 1119744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1120256 : Path.checkChunk context decode facts instructions 1120256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1120768 : Path.checkChunk context decode facts instructions 1120768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1121280 : Path.checkChunk context decode facts instructions 1121280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1121792 : Path.checkChunk context decode facts instructions 1121792 512 = true := by
  decide +kernel

theorem sound_1114112 (prior : ∀ n, n < 1114112 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1122304 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1114624 := Path.chunk_sound context_valid decode facts instructions 1114112 512
    prior checked_1114112
  have h1115136 := Path.chunk_sound context_valid decode facts instructions 1114624 512
    h1114624 checked_1114624
  have h1115648 := Path.chunk_sound context_valid decode facts instructions 1115136 512
    h1115136 checked_1115136
  have h1116160 := Path.chunk_sound context_valid decode facts instructions 1115648 512
    h1115648 checked_1115648
  have h1116672 := Path.chunk_sound context_valid decode facts instructions 1116160 512
    h1116160 checked_1116160
  have h1117184 := Path.chunk_sound context_valid decode facts instructions 1116672 512
    h1116672 checked_1116672
  have h1117696 := Path.chunk_sound context_valid decode facts instructions 1117184 512
    h1117184 checked_1117184
  have h1118208 := Path.chunk_sound context_valid decode facts instructions 1117696 512
    h1117696 checked_1117696
  have h1118720 := Path.chunk_sound context_valid decode facts instructions 1118208 512
    h1118208 checked_1118208
  have h1119232 := Path.chunk_sound context_valid decode facts instructions 1118720 512
    h1118720 checked_1118720
  have h1119744 := Path.chunk_sound context_valid decode facts instructions 1119232 512
    h1119232 checked_1119232
  have h1120256 := Path.chunk_sound context_valid decode facts instructions 1119744 512
    h1119744 checked_1119744
  have h1120768 := Path.chunk_sound context_valid decode facts instructions 1120256 512
    h1120256 checked_1120256
  have h1121280 := Path.chunk_sound context_valid decode facts instructions 1120768 512
    h1120768 checked_1120768
  have h1121792 := Path.chunk_sound context_valid decode facts instructions 1121280 512
    h1121280 checked_1121280
  have h1122304 := Path.chunk_sound context_valid decode facts instructions 1121792 512
    h1121792 checked_1121792
  exact h1122304

end Sporadic.Janko3.AmalgamPresentation.Cover
