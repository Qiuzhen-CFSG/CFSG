module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1433600 : Path.checkChunk context decode facts instructions 1433600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1434112 : Path.checkChunk context decode facts instructions 1434112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1434624 : Path.checkChunk context decode facts instructions 1434624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1435136 : Path.checkChunk context decode facts instructions 1435136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1435648 : Path.checkChunk context decode facts instructions 1435648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1436160 : Path.checkChunk context decode facts instructions 1436160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1436672 : Path.checkChunk context decode facts instructions 1436672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1437184 : Path.checkChunk context decode facts instructions 1437184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1437696 : Path.checkChunk context decode facts instructions 1437696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1438208 : Path.checkChunk context decode facts instructions 1438208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1438720 : Path.checkChunk context decode facts instructions 1438720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1439232 : Path.checkChunk context decode facts instructions 1439232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1439744 : Path.checkChunk context decode facts instructions 1439744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1440256 : Path.checkChunk context decode facts instructions 1440256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1440768 : Path.checkChunk context decode facts instructions 1440768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1441280 : Path.checkChunk context decode facts instructions 1441280 512 = true := by
  decide +kernel

theorem sound_1433600 (prior : ∀ n, n < 1433600 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1441792 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1434112 := Path.chunk_sound context_valid decode facts instructions 1433600 512
    prior checked_1433600
  have h1434624 := Path.chunk_sound context_valid decode facts instructions 1434112 512
    h1434112 checked_1434112
  have h1435136 := Path.chunk_sound context_valid decode facts instructions 1434624 512
    h1434624 checked_1434624
  have h1435648 := Path.chunk_sound context_valid decode facts instructions 1435136 512
    h1435136 checked_1435136
  have h1436160 := Path.chunk_sound context_valid decode facts instructions 1435648 512
    h1435648 checked_1435648
  have h1436672 := Path.chunk_sound context_valid decode facts instructions 1436160 512
    h1436160 checked_1436160
  have h1437184 := Path.chunk_sound context_valid decode facts instructions 1436672 512
    h1436672 checked_1436672
  have h1437696 := Path.chunk_sound context_valid decode facts instructions 1437184 512
    h1437184 checked_1437184
  have h1438208 := Path.chunk_sound context_valid decode facts instructions 1437696 512
    h1437696 checked_1437696
  have h1438720 := Path.chunk_sound context_valid decode facts instructions 1438208 512
    h1438208 checked_1438208
  have h1439232 := Path.chunk_sound context_valid decode facts instructions 1438720 512
    h1438720 checked_1438720
  have h1439744 := Path.chunk_sound context_valid decode facts instructions 1439232 512
    h1439232 checked_1439232
  have h1440256 := Path.chunk_sound context_valid decode facts instructions 1439744 512
    h1439744 checked_1439744
  have h1440768 := Path.chunk_sound context_valid decode facts instructions 1440256 512
    h1440256 checked_1440256
  have h1441280 := Path.chunk_sound context_valid decode facts instructions 1440768 512
    h1440768 checked_1440768
  have h1441792 := Path.chunk_sound context_valid decode facts instructions 1441280 512
    h1441280 checked_1441280
  exact h1441792

end Sporadic.Janko3.AmalgamPresentation.Cover
