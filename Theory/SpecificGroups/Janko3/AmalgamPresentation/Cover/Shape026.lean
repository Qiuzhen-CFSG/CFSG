module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_212992 : shapeChunk 212992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_213504 : shapeChunk 213504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_214016 : shapeChunk 214016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_214528 : shapeChunk 214528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_215040 : shapeChunk 215040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_215552 : shapeChunk 215552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_216064 : shapeChunk 216064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_216576 : shapeChunk 216576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_217088 : shapeChunk 217088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_217600 : shapeChunk 217600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_218112 : shapeChunk 218112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_218624 : shapeChunk 218624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_219136 : shapeChunk 219136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_219648 : shapeChunk 219648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_220160 : shapeChunk 220160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_220672 : shapeChunk 220672 512 = true := by
  decide +kernel

theorem shapes_212992 (n : Nat) (hlo : 212992 ≤ n) (hhi : n < 221184) : shapeAt n = true := by
  by_cases h212992 : n < 213504
  · exact shapeChunk_sound shaped_212992 n (by omega) h212992
  by_cases h213504 : n < 214016
  · exact shapeChunk_sound shaped_213504 n (by omega) h213504
  by_cases h214016 : n < 214528
  · exact shapeChunk_sound shaped_214016 n (by omega) h214016
  by_cases h214528 : n < 215040
  · exact shapeChunk_sound shaped_214528 n (by omega) h214528
  by_cases h215040 : n < 215552
  · exact shapeChunk_sound shaped_215040 n (by omega) h215040
  by_cases h215552 : n < 216064
  · exact shapeChunk_sound shaped_215552 n (by omega) h215552
  by_cases h216064 : n < 216576
  · exact shapeChunk_sound shaped_216064 n (by omega) h216064
  by_cases h216576 : n < 217088
  · exact shapeChunk_sound shaped_216576 n (by omega) h216576
  by_cases h217088 : n < 217600
  · exact shapeChunk_sound shaped_217088 n (by omega) h217088
  by_cases h217600 : n < 218112
  · exact shapeChunk_sound shaped_217600 n (by omega) h217600
  by_cases h218112 : n < 218624
  · exact shapeChunk_sound shaped_218112 n (by omega) h218112
  by_cases h218624 : n < 219136
  · exact shapeChunk_sound shaped_218624 n (by omega) h218624
  by_cases h219136 : n < 219648
  · exact shapeChunk_sound shaped_219136 n (by omega) h219136
  by_cases h219648 : n < 220160
  · exact shapeChunk_sound shaped_219648 n (by omega) h219648
  by_cases h220160 : n < 220672
  · exact shapeChunk_sound shaped_220160 n (by omega) h220160
  exact shapeChunk_sound shaped_220672 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
