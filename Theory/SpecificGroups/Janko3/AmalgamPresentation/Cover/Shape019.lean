module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_155648 : shapeChunk 155648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_156160 : shapeChunk 156160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_156672 : shapeChunk 156672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_157184 : shapeChunk 157184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_157696 : shapeChunk 157696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_158208 : shapeChunk 158208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_158720 : shapeChunk 158720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_159232 : shapeChunk 159232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_159744 : shapeChunk 159744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_160256 : shapeChunk 160256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_160768 : shapeChunk 160768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_161280 : shapeChunk 161280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_161792 : shapeChunk 161792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_162304 : shapeChunk 162304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_162816 : shapeChunk 162816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_163328 : shapeChunk 163328 512 = true := by
  decide +kernel

theorem shapes_155648 (n : Nat) (hlo : 155648 ≤ n) (hhi : n < 163840) : shapeAt n = true := by
  by_cases h155648 : n < 156160
  · exact shapeChunk_sound shaped_155648 n (by omega) h155648
  by_cases h156160 : n < 156672
  · exact shapeChunk_sound shaped_156160 n (by omega) h156160
  by_cases h156672 : n < 157184
  · exact shapeChunk_sound shaped_156672 n (by omega) h156672
  by_cases h157184 : n < 157696
  · exact shapeChunk_sound shaped_157184 n (by omega) h157184
  by_cases h157696 : n < 158208
  · exact shapeChunk_sound shaped_157696 n (by omega) h157696
  by_cases h158208 : n < 158720
  · exact shapeChunk_sound shaped_158208 n (by omega) h158208
  by_cases h158720 : n < 159232
  · exact shapeChunk_sound shaped_158720 n (by omega) h158720
  by_cases h159232 : n < 159744
  · exact shapeChunk_sound shaped_159232 n (by omega) h159232
  by_cases h159744 : n < 160256
  · exact shapeChunk_sound shaped_159744 n (by omega) h159744
  by_cases h160256 : n < 160768
  · exact shapeChunk_sound shaped_160256 n (by omega) h160256
  by_cases h160768 : n < 161280
  · exact shapeChunk_sound shaped_160768 n (by omega) h160768
  by_cases h161280 : n < 161792
  · exact shapeChunk_sound shaped_161280 n (by omega) h161280
  by_cases h161792 : n < 162304
  · exact shapeChunk_sound shaped_161792 n (by omega) h161792
  by_cases h162304 : n < 162816
  · exact shapeChunk_sound shaped_162304 n (by omega) h162304
  by_cases h162816 : n < 163328
  · exact shapeChunk_sound shaped_162816 n (by omega) h162816
  exact shapeChunk_sound shaped_163328 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
