module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_114688 : shapeChunk 114688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_115200 : shapeChunk 115200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_115712 : shapeChunk 115712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_116224 : shapeChunk 116224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_116736 : shapeChunk 116736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_117248 : shapeChunk 117248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_117760 : shapeChunk 117760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_118272 : shapeChunk 118272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_118784 : shapeChunk 118784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_119296 : shapeChunk 119296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_119808 : shapeChunk 119808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_120320 : shapeChunk 120320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_120832 : shapeChunk 120832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_121344 : shapeChunk 121344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_121856 : shapeChunk 121856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_122368 : shapeChunk 122368 512 = true := by
  decide +kernel

theorem shapes_114688 (n : Nat) (hlo : 114688 ≤ n) (hhi : n < 122880) : shapeAt n = true := by
  by_cases h114688 : n < 115200
  · exact shapeChunk_sound shaped_114688 n (by omega) h114688
  by_cases h115200 : n < 115712
  · exact shapeChunk_sound shaped_115200 n (by omega) h115200
  by_cases h115712 : n < 116224
  · exact shapeChunk_sound shaped_115712 n (by omega) h115712
  by_cases h116224 : n < 116736
  · exact shapeChunk_sound shaped_116224 n (by omega) h116224
  by_cases h116736 : n < 117248
  · exact shapeChunk_sound shaped_116736 n (by omega) h116736
  by_cases h117248 : n < 117760
  · exact shapeChunk_sound shaped_117248 n (by omega) h117248
  by_cases h117760 : n < 118272
  · exact shapeChunk_sound shaped_117760 n (by omega) h117760
  by_cases h118272 : n < 118784
  · exact shapeChunk_sound shaped_118272 n (by omega) h118272
  by_cases h118784 : n < 119296
  · exact shapeChunk_sound shaped_118784 n (by omega) h118784
  by_cases h119296 : n < 119808
  · exact shapeChunk_sound shaped_119296 n (by omega) h119296
  by_cases h119808 : n < 120320
  · exact shapeChunk_sound shaped_119808 n (by omega) h119808
  by_cases h120320 : n < 120832
  · exact shapeChunk_sound shaped_120320 n (by omega) h120320
  by_cases h120832 : n < 121344
  · exact shapeChunk_sound shaped_120832 n (by omega) h120832
  by_cases h121344 : n < 121856
  · exact shapeChunk_sound shaped_121344 n (by omega) h121344
  by_cases h121856 : n < 122368
  · exact shapeChunk_sound shaped_121856 n (by omega) h121856
  exact shapeChunk_sound shaped_122368 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
