module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_73728 : shapeChunk 73728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_74240 : shapeChunk 74240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_74752 : shapeChunk 74752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_75264 : shapeChunk 75264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_75776 : shapeChunk 75776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_76288 : shapeChunk 76288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_76800 : shapeChunk 76800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_77312 : shapeChunk 77312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_77824 : shapeChunk 77824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_78336 : shapeChunk 78336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_78848 : shapeChunk 78848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_79360 : shapeChunk 79360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_79872 : shapeChunk 79872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_80384 : shapeChunk 80384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_80896 : shapeChunk 80896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_81408 : shapeChunk 81408 512 = true := by
  decide +kernel

theorem shapes_73728 (n : Nat) (hlo : 73728 ≤ n) (hhi : n < 81920) : shapeAt n = true := by
  by_cases h73728 : n < 74240
  · exact shapeChunk_sound shaped_73728 n (by omega) h73728
  by_cases h74240 : n < 74752
  · exact shapeChunk_sound shaped_74240 n (by omega) h74240
  by_cases h74752 : n < 75264
  · exact shapeChunk_sound shaped_74752 n (by omega) h74752
  by_cases h75264 : n < 75776
  · exact shapeChunk_sound shaped_75264 n (by omega) h75264
  by_cases h75776 : n < 76288
  · exact shapeChunk_sound shaped_75776 n (by omega) h75776
  by_cases h76288 : n < 76800
  · exact shapeChunk_sound shaped_76288 n (by omega) h76288
  by_cases h76800 : n < 77312
  · exact shapeChunk_sound shaped_76800 n (by omega) h76800
  by_cases h77312 : n < 77824
  · exact shapeChunk_sound shaped_77312 n (by omega) h77312
  by_cases h77824 : n < 78336
  · exact shapeChunk_sound shaped_77824 n (by omega) h77824
  by_cases h78336 : n < 78848
  · exact shapeChunk_sound shaped_78336 n (by omega) h78336
  by_cases h78848 : n < 79360
  · exact shapeChunk_sound shaped_78848 n (by omega) h78848
  by_cases h79360 : n < 79872
  · exact shapeChunk_sound shaped_79360 n (by omega) h79360
  by_cases h79872 : n < 80384
  · exact shapeChunk_sound shaped_79872 n (by omega) h79872
  by_cases h80384 : n < 80896
  · exact shapeChunk_sound shaped_80384 n (by omega) h80384
  by_cases h80896 : n < 81408
  · exact shapeChunk_sound shaped_80896 n (by omega) h80896
  exact shapeChunk_sound shaped_81408 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
