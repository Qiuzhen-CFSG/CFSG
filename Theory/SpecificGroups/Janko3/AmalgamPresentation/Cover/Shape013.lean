module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_106496 : shapeChunk 106496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_107008 : shapeChunk 107008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_107520 : shapeChunk 107520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_108032 : shapeChunk 108032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_108544 : shapeChunk 108544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_109056 : shapeChunk 109056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_109568 : shapeChunk 109568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_110080 : shapeChunk 110080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_110592 : shapeChunk 110592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_111104 : shapeChunk 111104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_111616 : shapeChunk 111616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_112128 : shapeChunk 112128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_112640 : shapeChunk 112640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_113152 : shapeChunk 113152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_113664 : shapeChunk 113664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_114176 : shapeChunk 114176 512 = true := by
  decide +kernel

theorem shapes_106496 (n : Nat) (hlo : 106496 ≤ n) (hhi : n < 114688) : shapeAt n = true := by
  by_cases h106496 : n < 107008
  · exact shapeChunk_sound shaped_106496 n (by omega) h106496
  by_cases h107008 : n < 107520
  · exact shapeChunk_sound shaped_107008 n (by omega) h107008
  by_cases h107520 : n < 108032
  · exact shapeChunk_sound shaped_107520 n (by omega) h107520
  by_cases h108032 : n < 108544
  · exact shapeChunk_sound shaped_108032 n (by omega) h108032
  by_cases h108544 : n < 109056
  · exact shapeChunk_sound shaped_108544 n (by omega) h108544
  by_cases h109056 : n < 109568
  · exact shapeChunk_sound shaped_109056 n (by omega) h109056
  by_cases h109568 : n < 110080
  · exact shapeChunk_sound shaped_109568 n (by omega) h109568
  by_cases h110080 : n < 110592
  · exact shapeChunk_sound shaped_110080 n (by omega) h110080
  by_cases h110592 : n < 111104
  · exact shapeChunk_sound shaped_110592 n (by omega) h110592
  by_cases h111104 : n < 111616
  · exact shapeChunk_sound shaped_111104 n (by omega) h111104
  by_cases h111616 : n < 112128
  · exact shapeChunk_sound shaped_111616 n (by omega) h111616
  by_cases h112128 : n < 112640
  · exact shapeChunk_sound shaped_112128 n (by omega) h112128
  by_cases h112640 : n < 113152
  · exact shapeChunk_sound shaped_112640 n (by omega) h112640
  by_cases h113152 : n < 113664
  · exact shapeChunk_sound shaped_113152 n (by omega) h113152
  by_cases h113664 : n < 114176
  · exact shapeChunk_sound shaped_113664 n (by omega) h113664
  exact shapeChunk_sound shaped_114176 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
