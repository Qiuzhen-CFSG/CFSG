module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_139264 : shapeChunk 139264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_139776 : shapeChunk 139776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_140288 : shapeChunk 140288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_140800 : shapeChunk 140800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_141312 : shapeChunk 141312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_141824 : shapeChunk 141824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_142336 : shapeChunk 142336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_142848 : shapeChunk 142848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_143360 : shapeChunk 143360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_143872 : shapeChunk 143872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_144384 : shapeChunk 144384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_144896 : shapeChunk 144896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_145408 : shapeChunk 145408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_145920 : shapeChunk 145920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_146432 : shapeChunk 146432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_146944 : shapeChunk 146944 512 = true := by
  decide +kernel

theorem shapes_139264 (n : Nat) (hlo : 139264 ≤ n) (hhi : n < 147456) : shapeAt n = true := by
  by_cases h139264 : n < 139776
  · exact shapeChunk_sound shaped_139264 n (by omega) h139264
  by_cases h139776 : n < 140288
  · exact shapeChunk_sound shaped_139776 n (by omega) h139776
  by_cases h140288 : n < 140800
  · exact shapeChunk_sound shaped_140288 n (by omega) h140288
  by_cases h140800 : n < 141312
  · exact shapeChunk_sound shaped_140800 n (by omega) h140800
  by_cases h141312 : n < 141824
  · exact shapeChunk_sound shaped_141312 n (by omega) h141312
  by_cases h141824 : n < 142336
  · exact shapeChunk_sound shaped_141824 n (by omega) h141824
  by_cases h142336 : n < 142848
  · exact shapeChunk_sound shaped_142336 n (by omega) h142336
  by_cases h142848 : n < 143360
  · exact shapeChunk_sound shaped_142848 n (by omega) h142848
  by_cases h143360 : n < 143872
  · exact shapeChunk_sound shaped_143360 n (by omega) h143360
  by_cases h143872 : n < 144384
  · exact shapeChunk_sound shaped_143872 n (by omega) h143872
  by_cases h144384 : n < 144896
  · exact shapeChunk_sound shaped_144384 n (by omega) h144384
  by_cases h144896 : n < 145408
  · exact shapeChunk_sound shaped_144896 n (by omega) h144896
  by_cases h145408 : n < 145920
  · exact shapeChunk_sound shaped_145408 n (by omega) h145408
  by_cases h145920 : n < 146432
  · exact shapeChunk_sound shaped_145920 n (by omega) h145920
  by_cases h146432 : n < 146944
  · exact shapeChunk_sound shaped_146432 n (by omega) h146432
  exact shapeChunk_sound shaped_146944 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
