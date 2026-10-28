module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_81920 : shapeChunk 81920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_82432 : shapeChunk 82432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_82944 : shapeChunk 82944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_83456 : shapeChunk 83456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_83968 : shapeChunk 83968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_84480 : shapeChunk 84480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_84992 : shapeChunk 84992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_85504 : shapeChunk 85504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_86016 : shapeChunk 86016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_86528 : shapeChunk 86528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_87040 : shapeChunk 87040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_87552 : shapeChunk 87552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_88064 : shapeChunk 88064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_88576 : shapeChunk 88576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_89088 : shapeChunk 89088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_89600 : shapeChunk 89600 512 = true := by
  decide +kernel

theorem shapes_81920 (n : Nat) (hlo : 81920 ≤ n) (hhi : n < 90112) : shapeAt n = true := by
  by_cases h81920 : n < 82432
  · exact shapeChunk_sound shaped_81920 n (by omega) h81920
  by_cases h82432 : n < 82944
  · exact shapeChunk_sound shaped_82432 n (by omega) h82432
  by_cases h82944 : n < 83456
  · exact shapeChunk_sound shaped_82944 n (by omega) h82944
  by_cases h83456 : n < 83968
  · exact shapeChunk_sound shaped_83456 n (by omega) h83456
  by_cases h83968 : n < 84480
  · exact shapeChunk_sound shaped_83968 n (by omega) h83968
  by_cases h84480 : n < 84992
  · exact shapeChunk_sound shaped_84480 n (by omega) h84480
  by_cases h84992 : n < 85504
  · exact shapeChunk_sound shaped_84992 n (by omega) h84992
  by_cases h85504 : n < 86016
  · exact shapeChunk_sound shaped_85504 n (by omega) h85504
  by_cases h86016 : n < 86528
  · exact shapeChunk_sound shaped_86016 n (by omega) h86016
  by_cases h86528 : n < 87040
  · exact shapeChunk_sound shaped_86528 n (by omega) h86528
  by_cases h87040 : n < 87552
  · exact shapeChunk_sound shaped_87040 n (by omega) h87040
  by_cases h87552 : n < 88064
  · exact shapeChunk_sound shaped_87552 n (by omega) h87552
  by_cases h88064 : n < 88576
  · exact shapeChunk_sound shaped_88064 n (by omega) h88064
  by_cases h88576 : n < 89088
  · exact shapeChunk_sound shaped_88576 n (by omega) h88576
  by_cases h89088 : n < 89600
  · exact shapeChunk_sound shaped_89088 n (by omega) h89088
  exact shapeChunk_sound shaped_89600 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
