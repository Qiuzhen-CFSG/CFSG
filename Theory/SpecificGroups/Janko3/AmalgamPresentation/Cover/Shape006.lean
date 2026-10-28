module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_49152 : shapeChunk 49152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_49664 : shapeChunk 49664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_50176 : shapeChunk 50176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_50688 : shapeChunk 50688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_51200 : shapeChunk 51200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_51712 : shapeChunk 51712 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_52224 : shapeChunk 52224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_52736 : shapeChunk 52736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_53248 : shapeChunk 53248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_53760 : shapeChunk 53760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_54272 : shapeChunk 54272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_54784 : shapeChunk 54784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_55296 : shapeChunk 55296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_55808 : shapeChunk 55808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_56320 : shapeChunk 56320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_56832 : shapeChunk 56832 512 = true := by
  decide +kernel

theorem shapes_49152 (n : Nat) (hlo : 49152 ≤ n) (hhi : n < 57344) : shapeAt n = true := by
  by_cases h49152 : n < 49664
  · exact shapeChunk_sound shaped_49152 n (by omega) h49152
  by_cases h49664 : n < 50176
  · exact shapeChunk_sound shaped_49664 n (by omega) h49664
  by_cases h50176 : n < 50688
  · exact shapeChunk_sound shaped_50176 n (by omega) h50176
  by_cases h50688 : n < 51200
  · exact shapeChunk_sound shaped_50688 n (by omega) h50688
  by_cases h51200 : n < 51712
  · exact shapeChunk_sound shaped_51200 n (by omega) h51200
  by_cases h51712 : n < 52224
  · exact shapeChunk_sound shaped_51712 n (by omega) h51712
  by_cases h52224 : n < 52736
  · exact shapeChunk_sound shaped_52224 n (by omega) h52224
  by_cases h52736 : n < 53248
  · exact shapeChunk_sound shaped_52736 n (by omega) h52736
  by_cases h53248 : n < 53760
  · exact shapeChunk_sound shaped_53248 n (by omega) h53248
  by_cases h53760 : n < 54272
  · exact shapeChunk_sound shaped_53760 n (by omega) h53760
  by_cases h54272 : n < 54784
  · exact shapeChunk_sound shaped_54272 n (by omega) h54272
  by_cases h54784 : n < 55296
  · exact shapeChunk_sound shaped_54784 n (by omega) h54784
  by_cases h55296 : n < 55808
  · exact shapeChunk_sound shaped_55296 n (by omega) h55296
  by_cases h55808 : n < 56320
  · exact shapeChunk_sound shaped_55808 n (by omega) h55808
  by_cases h56320 : n < 56832
  · exact shapeChunk_sound shaped_56320 n (by omega) h56320
  exact shapeChunk_sound shaped_56832 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
