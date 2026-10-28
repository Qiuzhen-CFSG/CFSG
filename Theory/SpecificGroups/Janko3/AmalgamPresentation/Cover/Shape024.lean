module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_196608 : shapeChunk 196608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_197120 : shapeChunk 197120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_197632 : shapeChunk 197632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_198144 : shapeChunk 198144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_198656 : shapeChunk 198656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_199168 : shapeChunk 199168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_199680 : shapeChunk 199680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_200192 : shapeChunk 200192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_200704 : shapeChunk 200704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_201216 : shapeChunk 201216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_201728 : shapeChunk 201728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_202240 : shapeChunk 202240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_202752 : shapeChunk 202752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_203264 : shapeChunk 203264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_203776 : shapeChunk 203776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_204288 : shapeChunk 204288 512 = true := by
  decide +kernel

theorem shapes_196608 (n : Nat) (hlo : 196608 ≤ n) (hhi : n < 204800) : shapeAt n = true := by
  by_cases h196608 : n < 197120
  · exact shapeChunk_sound shaped_196608 n (by omega) h196608
  by_cases h197120 : n < 197632
  · exact shapeChunk_sound shaped_197120 n (by omega) h197120
  by_cases h197632 : n < 198144
  · exact shapeChunk_sound shaped_197632 n (by omega) h197632
  by_cases h198144 : n < 198656
  · exact shapeChunk_sound shaped_198144 n (by omega) h198144
  by_cases h198656 : n < 199168
  · exact shapeChunk_sound shaped_198656 n (by omega) h198656
  by_cases h199168 : n < 199680
  · exact shapeChunk_sound shaped_199168 n (by omega) h199168
  by_cases h199680 : n < 200192
  · exact shapeChunk_sound shaped_199680 n (by omega) h199680
  by_cases h200192 : n < 200704
  · exact shapeChunk_sound shaped_200192 n (by omega) h200192
  by_cases h200704 : n < 201216
  · exact shapeChunk_sound shaped_200704 n (by omega) h200704
  by_cases h201216 : n < 201728
  · exact shapeChunk_sound shaped_201216 n (by omega) h201216
  by_cases h201728 : n < 202240
  · exact shapeChunk_sound shaped_201728 n (by omega) h201728
  by_cases h202240 : n < 202752
  · exact shapeChunk_sound shaped_202240 n (by omega) h202240
  by_cases h202752 : n < 203264
  · exact shapeChunk_sound shaped_202752 n (by omega) h202752
  by_cases h203264 : n < 203776
  · exact shapeChunk_sound shaped_203264 n (by omega) h203264
  by_cases h203776 : n < 204288
  · exact shapeChunk_sound shaped_203776 n (by omega) h203776
  exact shapeChunk_sound shaped_204288 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
