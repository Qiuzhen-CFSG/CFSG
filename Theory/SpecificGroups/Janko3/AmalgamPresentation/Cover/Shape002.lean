module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_16384 : shapeChunk 16384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_16896 : shapeChunk 16896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_17408 : shapeChunk 17408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_17920 : shapeChunk 17920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_18432 : shapeChunk 18432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_18944 : shapeChunk 18944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_19456 : shapeChunk 19456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_19968 : shapeChunk 19968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_20480 : shapeChunk 20480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_20992 : shapeChunk 20992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_21504 : shapeChunk 21504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_22016 : shapeChunk 22016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_22528 : shapeChunk 22528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_23040 : shapeChunk 23040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_23552 : shapeChunk 23552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_24064 : shapeChunk 24064 512 = true := by
  decide +kernel

theorem shapes_16384 (n : Nat) (hlo : 16384 ≤ n) (hhi : n < 24576) : shapeAt n = true := by
  by_cases h16384 : n < 16896
  · exact shapeChunk_sound shaped_16384 n (by omega) h16384
  by_cases h16896 : n < 17408
  · exact shapeChunk_sound shaped_16896 n (by omega) h16896
  by_cases h17408 : n < 17920
  · exact shapeChunk_sound shaped_17408 n (by omega) h17408
  by_cases h17920 : n < 18432
  · exact shapeChunk_sound shaped_17920 n (by omega) h17920
  by_cases h18432 : n < 18944
  · exact shapeChunk_sound shaped_18432 n (by omega) h18432
  by_cases h18944 : n < 19456
  · exact shapeChunk_sound shaped_18944 n (by omega) h18944
  by_cases h19456 : n < 19968
  · exact shapeChunk_sound shaped_19456 n (by omega) h19456
  by_cases h19968 : n < 20480
  · exact shapeChunk_sound shaped_19968 n (by omega) h19968
  by_cases h20480 : n < 20992
  · exact shapeChunk_sound shaped_20480 n (by omega) h20480
  by_cases h20992 : n < 21504
  · exact shapeChunk_sound shaped_20992 n (by omega) h20992
  by_cases h21504 : n < 22016
  · exact shapeChunk_sound shaped_21504 n (by omega) h21504
  by_cases h22016 : n < 22528
  · exact shapeChunk_sound shaped_22016 n (by omega) h22016
  by_cases h22528 : n < 23040
  · exact shapeChunk_sound shaped_22528 n (by omega) h22528
  by_cases h23040 : n < 23552
  · exact shapeChunk_sound shaped_23040 n (by omega) h23040
  by_cases h23552 : n < 24064
  · exact shapeChunk_sound shaped_23552 n (by omega) h23552
  exact shapeChunk_sound shaped_24064 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
