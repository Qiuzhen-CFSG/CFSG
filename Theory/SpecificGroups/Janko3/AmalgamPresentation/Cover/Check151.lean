module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1236992 : Path.checkChunk context decode facts instructions 1236992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1237504 : Path.checkChunk context decode facts instructions 1237504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1238016 : Path.checkChunk context decode facts instructions 1238016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1238528 : Path.checkChunk context decode facts instructions 1238528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1239040 : Path.checkChunk context decode facts instructions 1239040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1239552 : Path.checkChunk context decode facts instructions 1239552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1240064 : Path.checkChunk context decode facts instructions 1240064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1240576 : Path.checkChunk context decode facts instructions 1240576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1241088 : Path.checkChunk context decode facts instructions 1241088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1241600 : Path.checkChunk context decode facts instructions 1241600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1242112 : Path.checkChunk context decode facts instructions 1242112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1242624 : Path.checkChunk context decode facts instructions 1242624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1243136 : Path.checkChunk context decode facts instructions 1243136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1243648 : Path.checkChunk context decode facts instructions 1243648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1244160 : Path.checkChunk context decode facts instructions 1244160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1244672 : Path.checkChunk context decode facts instructions 1244672 512 = true := by
  decide +kernel

theorem sound_1236992 (prior : ∀ n, n < 1236992 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1245184 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1237504 := Path.chunk_sound context_valid decode facts instructions 1236992 512
    prior checked_1236992
  have h1238016 := Path.chunk_sound context_valid decode facts instructions 1237504 512
    h1237504 checked_1237504
  have h1238528 := Path.chunk_sound context_valid decode facts instructions 1238016 512
    h1238016 checked_1238016
  have h1239040 := Path.chunk_sound context_valid decode facts instructions 1238528 512
    h1238528 checked_1238528
  have h1239552 := Path.chunk_sound context_valid decode facts instructions 1239040 512
    h1239040 checked_1239040
  have h1240064 := Path.chunk_sound context_valid decode facts instructions 1239552 512
    h1239552 checked_1239552
  have h1240576 := Path.chunk_sound context_valid decode facts instructions 1240064 512
    h1240064 checked_1240064
  have h1241088 := Path.chunk_sound context_valid decode facts instructions 1240576 512
    h1240576 checked_1240576
  have h1241600 := Path.chunk_sound context_valid decode facts instructions 1241088 512
    h1241088 checked_1241088
  have h1242112 := Path.chunk_sound context_valid decode facts instructions 1241600 512
    h1241600 checked_1241600
  have h1242624 := Path.chunk_sound context_valid decode facts instructions 1242112 512
    h1242112 checked_1242112
  have h1243136 := Path.chunk_sound context_valid decode facts instructions 1242624 512
    h1242624 checked_1242624
  have h1243648 := Path.chunk_sound context_valid decode facts instructions 1243136 512
    h1243136 checked_1243136
  have h1244160 := Path.chunk_sound context_valid decode facts instructions 1243648 512
    h1243648 checked_1243648
  have h1244672 := Path.chunk_sound context_valid decode facts instructions 1244160 512
    h1244160 checked_1244160
  have h1245184 := Path.chunk_sound context_valid decode facts instructions 1244672 512
    h1244672 checked_1244672
  exact h1245184

end Sporadic.Janko3.AmalgamPresentation.Cover
