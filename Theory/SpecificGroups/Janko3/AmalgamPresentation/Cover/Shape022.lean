module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_180224 : shapeChunk 180224 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_180736 : shapeChunk 180736 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_181248 : shapeChunk 181248 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_181760 : shapeChunk 181760 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_182272 : shapeChunk 182272 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_182784 : shapeChunk 182784 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_183296 : shapeChunk 183296 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_183808 : shapeChunk 183808 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_184320 : shapeChunk 184320 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_184832 : shapeChunk 184832 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_185344 : shapeChunk 185344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_185856 : shapeChunk 185856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_186368 : shapeChunk 186368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_186880 : shapeChunk 186880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_187392 : shapeChunk 187392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_187904 : shapeChunk 187904 512 = true := by
  decide +kernel

theorem shapes_180224 (n : Nat) (hlo : 180224 ≤ n) (hhi : n < 188416) : shapeAt n = true := by
  by_cases h180224 : n < 180736
  · exact shapeChunk_sound shaped_180224 n (by omega) h180224
  by_cases h180736 : n < 181248
  · exact shapeChunk_sound shaped_180736 n (by omega) h180736
  by_cases h181248 : n < 181760
  · exact shapeChunk_sound shaped_181248 n (by omega) h181248
  by_cases h181760 : n < 182272
  · exact shapeChunk_sound shaped_181760 n (by omega) h181760
  by_cases h182272 : n < 182784
  · exact shapeChunk_sound shaped_182272 n (by omega) h182272
  by_cases h182784 : n < 183296
  · exact shapeChunk_sound shaped_182784 n (by omega) h182784
  by_cases h183296 : n < 183808
  · exact shapeChunk_sound shaped_183296 n (by omega) h183296
  by_cases h183808 : n < 184320
  · exact shapeChunk_sound shaped_183808 n (by omega) h183808
  by_cases h184320 : n < 184832
  · exact shapeChunk_sound shaped_184320 n (by omega) h184320
  by_cases h184832 : n < 185344
  · exact shapeChunk_sound shaped_184832 n (by omega) h184832
  by_cases h185344 : n < 185856
  · exact shapeChunk_sound shaped_185344 n (by omega) h185344
  by_cases h185856 : n < 186368
  · exact shapeChunk_sound shaped_185856 n (by omega) h185856
  by_cases h186368 : n < 186880
  · exact shapeChunk_sound shaped_186368 n (by omega) h186368
  by_cases h186880 : n < 187392
  · exact shapeChunk_sound shaped_186880 n (by omega) h186880
  by_cases h187392 : n < 187904
  · exact shapeChunk_sound shaped_187392 n (by omega) h187392
  exact shapeChunk_sound shaped_187904 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
