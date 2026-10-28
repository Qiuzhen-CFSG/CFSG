module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_204800 : shapeChunk 204800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_205312 : shapeChunk 205312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_205824 : shapeChunk 205824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_206336 : shapeChunk 206336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_206848 : shapeChunk 206848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_207360 : shapeChunk 207360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_207872 : shapeChunk 207872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_208384 : shapeChunk 208384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_208896 : shapeChunk 208896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_209408 : shapeChunk 209408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_209920 : shapeChunk 209920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_210432 : shapeChunk 210432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_210944 : shapeChunk 210944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_211456 : shapeChunk 211456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_211968 : shapeChunk 211968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_212480 : shapeChunk 212480 512 = true := by
  decide +kernel

theorem shapes_204800 (n : Nat) (hlo : 204800 ≤ n) (hhi : n < 212992) : shapeAt n = true := by
  by_cases h204800 : n < 205312
  · exact shapeChunk_sound shaped_204800 n (by omega) h204800
  by_cases h205312 : n < 205824
  · exact shapeChunk_sound shaped_205312 n (by omega) h205312
  by_cases h205824 : n < 206336
  · exact shapeChunk_sound shaped_205824 n (by omega) h205824
  by_cases h206336 : n < 206848
  · exact shapeChunk_sound shaped_206336 n (by omega) h206336
  by_cases h206848 : n < 207360
  · exact shapeChunk_sound shaped_206848 n (by omega) h206848
  by_cases h207360 : n < 207872
  · exact shapeChunk_sound shaped_207360 n (by omega) h207360
  by_cases h207872 : n < 208384
  · exact shapeChunk_sound shaped_207872 n (by omega) h207872
  by_cases h208384 : n < 208896
  · exact shapeChunk_sound shaped_208384 n (by omega) h208384
  by_cases h208896 : n < 209408
  · exact shapeChunk_sound shaped_208896 n (by omega) h208896
  by_cases h209408 : n < 209920
  · exact shapeChunk_sound shaped_209408 n (by omega) h209408
  by_cases h209920 : n < 210432
  · exact shapeChunk_sound shaped_209920 n (by omega) h209920
  by_cases h210432 : n < 210944
  · exact shapeChunk_sound shaped_210432 n (by omega) h210432
  by_cases h210944 : n < 211456
  · exact shapeChunk_sound shaped_210944 n (by omega) h210944
  by_cases h211456 : n < 211968
  · exact shapeChunk_sound shaped_211456 n (by omega) h211456
  by_cases h211968 : n < 212480
  · exact shapeChunk_sound shaped_211968 n (by omega) h211968
  exact shapeChunk_sound shaped_212480 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
