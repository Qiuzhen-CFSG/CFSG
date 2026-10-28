module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_983040 : Path.checkChunk context decode facts instructions 983040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_983552 : Path.checkChunk context decode facts instructions 983552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_984064 : Path.checkChunk context decode facts instructions 984064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_984576 : Path.checkChunk context decode facts instructions 984576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_985088 : Path.checkChunk context decode facts instructions 985088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_985600 : Path.checkChunk context decode facts instructions 985600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_986112 : Path.checkChunk context decode facts instructions 986112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_986624 : Path.checkChunk context decode facts instructions 986624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_987136 : Path.checkChunk context decode facts instructions 987136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_987648 : Path.checkChunk context decode facts instructions 987648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_988160 : Path.checkChunk context decode facts instructions 988160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_988672 : Path.checkChunk context decode facts instructions 988672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_989184 : Path.checkChunk context decode facts instructions 989184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_989696 : Path.checkChunk context decode facts instructions 989696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_990208 : Path.checkChunk context decode facts instructions 990208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_990720 : Path.checkChunk context decode facts instructions 990720 512 = true := by
  decide +kernel

theorem sound_983040 (prior : ∀ n, n < 983040 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 991232 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h983552 := Path.chunk_sound context_valid decode facts instructions 983040 512
    prior checked_983040
  have h984064 := Path.chunk_sound context_valid decode facts instructions 983552 512
    h983552 checked_983552
  have h984576 := Path.chunk_sound context_valid decode facts instructions 984064 512
    h984064 checked_984064
  have h985088 := Path.chunk_sound context_valid decode facts instructions 984576 512
    h984576 checked_984576
  have h985600 := Path.chunk_sound context_valid decode facts instructions 985088 512
    h985088 checked_985088
  have h986112 := Path.chunk_sound context_valid decode facts instructions 985600 512
    h985600 checked_985600
  have h986624 := Path.chunk_sound context_valid decode facts instructions 986112 512
    h986112 checked_986112
  have h987136 := Path.chunk_sound context_valid decode facts instructions 986624 512
    h986624 checked_986624
  have h987648 := Path.chunk_sound context_valid decode facts instructions 987136 512
    h987136 checked_987136
  have h988160 := Path.chunk_sound context_valid decode facts instructions 987648 512
    h987648 checked_987648
  have h988672 := Path.chunk_sound context_valid decode facts instructions 988160 512
    h988160 checked_988160
  have h989184 := Path.chunk_sound context_valid decode facts instructions 988672 512
    h988672 checked_988672
  have h989696 := Path.chunk_sound context_valid decode facts instructions 989184 512
    h989184 checked_989184
  have h990208 := Path.chunk_sound context_valid decode facts instructions 989696 512
    h989696 checked_989696
  have h990720 := Path.chunk_sound context_valid decode facts instructions 990208 512
    h990208 checked_990208
  have h991232 := Path.chunk_sound context_valid decode facts instructions 990720 512
    h990720 checked_990720
  exact h991232

end Sporadic.Janko3.AmalgamPresentation.Cover
