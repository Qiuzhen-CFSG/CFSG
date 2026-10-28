module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_131072 : shapeChunk 131072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_131584 : shapeChunk 131584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_132096 : shapeChunk 132096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_132608 : shapeChunk 132608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_133120 : shapeChunk 133120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_133632 : shapeChunk 133632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_134144 : shapeChunk 134144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_134656 : shapeChunk 134656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_135168 : shapeChunk 135168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_135680 : shapeChunk 135680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_136192 : shapeChunk 136192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_136704 : shapeChunk 136704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_137216 : shapeChunk 137216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_137728 : shapeChunk 137728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_138240 : shapeChunk 138240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_138752 : shapeChunk 138752 512 = true := by
  decide +kernel

theorem shapes_131072 (n : Nat) (hlo : 131072 ≤ n) (hhi : n < 139264) : shapeAt n = true := by
  by_cases h131072 : n < 131584
  · exact shapeChunk_sound shaped_131072 n (by omega) h131072
  by_cases h131584 : n < 132096
  · exact shapeChunk_sound shaped_131584 n (by omega) h131584
  by_cases h132096 : n < 132608
  · exact shapeChunk_sound shaped_132096 n (by omega) h132096
  by_cases h132608 : n < 133120
  · exact shapeChunk_sound shaped_132608 n (by omega) h132608
  by_cases h133120 : n < 133632
  · exact shapeChunk_sound shaped_133120 n (by omega) h133120
  by_cases h133632 : n < 134144
  · exact shapeChunk_sound shaped_133632 n (by omega) h133632
  by_cases h134144 : n < 134656
  · exact shapeChunk_sound shaped_134144 n (by omega) h134144
  by_cases h134656 : n < 135168
  · exact shapeChunk_sound shaped_134656 n (by omega) h134656
  by_cases h135168 : n < 135680
  · exact shapeChunk_sound shaped_135168 n (by omega) h135168
  by_cases h135680 : n < 136192
  · exact shapeChunk_sound shaped_135680 n (by omega) h135680
  by_cases h136192 : n < 136704
  · exact shapeChunk_sound shaped_136192 n (by omega) h136192
  by_cases h136704 : n < 137216
  · exact shapeChunk_sound shaped_136704 n (by omega) h136704
  by_cases h137216 : n < 137728
  · exact shapeChunk_sound shaped_137216 n (by omega) h137216
  by_cases h137728 : n < 138240
  · exact shapeChunk_sound shaped_137728 n (by omega) h137728
  by_cases h138240 : n < 138752
  · exact shapeChunk_sound shaped_138240 n (by omega) h138240
  exact shapeChunk_sound shaped_138752 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
