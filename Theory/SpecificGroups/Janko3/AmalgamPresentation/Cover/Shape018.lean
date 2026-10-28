module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_147456 : shapeChunk 147456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_147968 : shapeChunk 147968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_148480 : shapeChunk 148480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_148992 : shapeChunk 148992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_149504 : shapeChunk 149504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_150016 : shapeChunk 150016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_150528 : shapeChunk 150528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_151040 : shapeChunk 151040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_151552 : shapeChunk 151552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_152064 : shapeChunk 152064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_152576 : shapeChunk 152576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_153088 : shapeChunk 153088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_153600 : shapeChunk 153600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_154112 : shapeChunk 154112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_154624 : shapeChunk 154624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_155136 : shapeChunk 155136 512 = true := by
  decide +kernel

theorem shapes_147456 (n : Nat) (hlo : 147456 ≤ n) (hhi : n < 155648) : shapeAt n = true := by
  by_cases h147456 : n < 147968
  · exact shapeChunk_sound shaped_147456 n (by omega) h147456
  by_cases h147968 : n < 148480
  · exact shapeChunk_sound shaped_147968 n (by omega) h147968
  by_cases h148480 : n < 148992
  · exact shapeChunk_sound shaped_148480 n (by omega) h148480
  by_cases h148992 : n < 149504
  · exact shapeChunk_sound shaped_148992 n (by omega) h148992
  by_cases h149504 : n < 150016
  · exact shapeChunk_sound shaped_149504 n (by omega) h149504
  by_cases h150016 : n < 150528
  · exact shapeChunk_sound shaped_150016 n (by omega) h150016
  by_cases h150528 : n < 151040
  · exact shapeChunk_sound shaped_150528 n (by omega) h150528
  by_cases h151040 : n < 151552
  · exact shapeChunk_sound shaped_151040 n (by omega) h151040
  by_cases h151552 : n < 152064
  · exact shapeChunk_sound shaped_151552 n (by omega) h151552
  by_cases h152064 : n < 152576
  · exact shapeChunk_sound shaped_152064 n (by omega) h152064
  by_cases h152576 : n < 153088
  · exact shapeChunk_sound shaped_152576 n (by omega) h152576
  by_cases h153088 : n < 153600
  · exact shapeChunk_sound shaped_153088 n (by omega) h153088
  by_cases h153600 : n < 154112
  · exact shapeChunk_sound shaped_153600 n (by omega) h153600
  by_cases h154112 : n < 154624
  · exact shapeChunk_sound shaped_154112 n (by omega) h154112
  by_cases h154624 : n < 155136
  · exact shapeChunk_sound shaped_154624 n (by omega) h154624
  exact shapeChunk_sound shaped_155136 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
