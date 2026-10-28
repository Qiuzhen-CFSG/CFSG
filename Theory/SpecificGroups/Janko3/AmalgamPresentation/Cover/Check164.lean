module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1343488 : Path.checkChunk context decode facts instructions 1343488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1344000 : Path.checkChunk context decode facts instructions 1344000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1344512 : Path.checkChunk context decode facts instructions 1344512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1345024 : Path.checkChunk context decode facts instructions 1345024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1345536 : Path.checkChunk context decode facts instructions 1345536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1346048 : Path.checkChunk context decode facts instructions 1346048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1346560 : Path.checkChunk context decode facts instructions 1346560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1347072 : Path.checkChunk context decode facts instructions 1347072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1347584 : Path.checkChunk context decode facts instructions 1347584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1348096 : Path.checkChunk context decode facts instructions 1348096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1348608 : Path.checkChunk context decode facts instructions 1348608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1349120 : Path.checkChunk context decode facts instructions 1349120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1349632 : Path.checkChunk context decode facts instructions 1349632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1350144 : Path.checkChunk context decode facts instructions 1350144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1350656 : Path.checkChunk context decode facts instructions 1350656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1351168 : Path.checkChunk context decode facts instructions 1351168 512 = true := by
  decide +kernel

theorem sound_1343488 (prior : ∀ n, n < 1343488 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1351680 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1344000 := Path.chunk_sound context_valid decode facts instructions 1343488 512
    prior checked_1343488
  have h1344512 := Path.chunk_sound context_valid decode facts instructions 1344000 512
    h1344000 checked_1344000
  have h1345024 := Path.chunk_sound context_valid decode facts instructions 1344512 512
    h1344512 checked_1344512
  have h1345536 := Path.chunk_sound context_valid decode facts instructions 1345024 512
    h1345024 checked_1345024
  have h1346048 := Path.chunk_sound context_valid decode facts instructions 1345536 512
    h1345536 checked_1345536
  have h1346560 := Path.chunk_sound context_valid decode facts instructions 1346048 512
    h1346048 checked_1346048
  have h1347072 := Path.chunk_sound context_valid decode facts instructions 1346560 512
    h1346560 checked_1346560
  have h1347584 := Path.chunk_sound context_valid decode facts instructions 1347072 512
    h1347072 checked_1347072
  have h1348096 := Path.chunk_sound context_valid decode facts instructions 1347584 512
    h1347584 checked_1347584
  have h1348608 := Path.chunk_sound context_valid decode facts instructions 1348096 512
    h1348096 checked_1348096
  have h1349120 := Path.chunk_sound context_valid decode facts instructions 1348608 512
    h1348608 checked_1348608
  have h1349632 := Path.chunk_sound context_valid decode facts instructions 1349120 512
    h1349120 checked_1349120
  have h1350144 := Path.chunk_sound context_valid decode facts instructions 1349632 512
    h1349632 checked_1349632
  have h1350656 := Path.chunk_sound context_valid decode facts instructions 1350144 512
    h1350144 checked_1350144
  have h1351168 := Path.chunk_sound context_valid decode facts instructions 1350656 512
    h1350656 checked_1350656
  have h1351680 := Path.chunk_sound context_valid decode facts instructions 1351168 512
    h1351168 checked_1351168
  exact h1351680

end Sporadic.Janko3.AmalgamPresentation.Cover
