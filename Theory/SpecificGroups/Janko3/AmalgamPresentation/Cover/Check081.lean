module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_663552 : Path.checkChunk context decode facts instructions 663552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_664064 : Path.checkChunk context decode facts instructions 664064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_664576 : Path.checkChunk context decode facts instructions 664576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_665088 : Path.checkChunk context decode facts instructions 665088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_665600 : Path.checkChunk context decode facts instructions 665600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_666112 : Path.checkChunk context decode facts instructions 666112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_666624 : Path.checkChunk context decode facts instructions 666624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_667136 : Path.checkChunk context decode facts instructions 667136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_667648 : Path.checkChunk context decode facts instructions 667648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_668160 : Path.checkChunk context decode facts instructions 668160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_668672 : Path.checkChunk context decode facts instructions 668672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_669184 : Path.checkChunk context decode facts instructions 669184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_669696 : Path.checkChunk context decode facts instructions 669696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_670208 : Path.checkChunk context decode facts instructions 670208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_670720 : Path.checkChunk context decode facts instructions 670720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_671232 : Path.checkChunk context decode facts instructions 671232 512 = true := by
  decide +kernel

theorem sound_663552 (prior : ∀ n, n < 663552 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 671744 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h664064 := Path.chunk_sound context_valid decode facts instructions 663552 512
    prior checked_663552
  have h664576 := Path.chunk_sound context_valid decode facts instructions 664064 512
    h664064 checked_664064
  have h665088 := Path.chunk_sound context_valid decode facts instructions 664576 512
    h664576 checked_664576
  have h665600 := Path.chunk_sound context_valid decode facts instructions 665088 512
    h665088 checked_665088
  have h666112 := Path.chunk_sound context_valid decode facts instructions 665600 512
    h665600 checked_665600
  have h666624 := Path.chunk_sound context_valid decode facts instructions 666112 512
    h666112 checked_666112
  have h667136 := Path.chunk_sound context_valid decode facts instructions 666624 512
    h666624 checked_666624
  have h667648 := Path.chunk_sound context_valid decode facts instructions 667136 512
    h667136 checked_667136
  have h668160 := Path.chunk_sound context_valid decode facts instructions 667648 512
    h667648 checked_667648
  have h668672 := Path.chunk_sound context_valid decode facts instructions 668160 512
    h668160 checked_668160
  have h669184 := Path.chunk_sound context_valid decode facts instructions 668672 512
    h668672 checked_668672
  have h669696 := Path.chunk_sound context_valid decode facts instructions 669184 512
    h669184 checked_669184
  have h670208 := Path.chunk_sound context_valid decode facts instructions 669696 512
    h669696 checked_669696
  have h670720 := Path.chunk_sound context_valid decode facts instructions 670208 512
    h670208 checked_670208
  have h671232 := Path.chunk_sound context_valid decode facts instructions 670720 512
    h670720 checked_670720
  have h671744 := Path.chunk_sound context_valid decode facts instructions 671232 512
    h671232 checked_671232
  exact h671744

end Sporadic.Janko3.AmalgamPresentation.Cover
