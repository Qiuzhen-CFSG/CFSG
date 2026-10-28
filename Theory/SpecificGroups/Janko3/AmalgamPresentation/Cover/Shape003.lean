module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_24576 : shapeChunk 24576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_25088 : shapeChunk 25088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_25600 : shapeChunk 25600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_26112 : shapeChunk 26112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_26624 : shapeChunk 26624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_27136 : shapeChunk 27136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_27648 : shapeChunk 27648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_28160 : shapeChunk 28160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_28672 : shapeChunk 28672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_29184 : shapeChunk 29184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_29696 : shapeChunk 29696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_30208 : shapeChunk 30208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_30720 : shapeChunk 30720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_31232 : shapeChunk 31232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_31744 : shapeChunk 31744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_32256 : shapeChunk 32256 512 = true := by
  decide +kernel

theorem shapes_24576 (n : Nat) (hlo : 24576 ≤ n) (hhi : n < 32768) : shapeAt n = true := by
  by_cases h24576 : n < 25088
  · exact shapeChunk_sound shaped_24576 n (by omega) h24576
  by_cases h25088 : n < 25600
  · exact shapeChunk_sound shaped_25088 n (by omega) h25088
  by_cases h25600 : n < 26112
  · exact shapeChunk_sound shaped_25600 n (by omega) h25600
  by_cases h26112 : n < 26624
  · exact shapeChunk_sound shaped_26112 n (by omega) h26112
  by_cases h26624 : n < 27136
  · exact shapeChunk_sound shaped_26624 n (by omega) h26624
  by_cases h27136 : n < 27648
  · exact shapeChunk_sound shaped_27136 n (by omega) h27136
  by_cases h27648 : n < 28160
  · exact shapeChunk_sound shaped_27648 n (by omega) h27648
  by_cases h28160 : n < 28672
  · exact shapeChunk_sound shaped_28160 n (by omega) h28160
  by_cases h28672 : n < 29184
  · exact shapeChunk_sound shaped_28672 n (by omega) h28672
  by_cases h29184 : n < 29696
  · exact shapeChunk_sound shaped_29184 n (by omega) h29184
  by_cases h29696 : n < 30208
  · exact shapeChunk_sound shaped_29696 n (by omega) h29696
  by_cases h30208 : n < 30720
  · exact shapeChunk_sound shaped_30208 n (by omega) h30208
  by_cases h30720 : n < 31232
  · exact shapeChunk_sound shaped_30720 n (by omega) h30720
  by_cases h31232 : n < 31744
  · exact shapeChunk_sound shaped_31232 n (by omega) h31232
  by_cases h31744 : n < 32256
  · exact shapeChunk_sound shaped_31744 n (by omega) h31744
  exact shapeChunk_sound shaped_32256 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
