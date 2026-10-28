module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_0 : shapeChunk 0 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_512 : shapeChunk 512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_1024 : shapeChunk 1024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_1536 : shapeChunk 1536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_2048 : shapeChunk 2048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_2560 : shapeChunk 2560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_3072 : shapeChunk 3072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_3584 : shapeChunk 3584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_4096 : shapeChunk 4096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_4608 : shapeChunk 4608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_5120 : shapeChunk 5120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_5632 : shapeChunk 5632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_6144 : shapeChunk 6144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_6656 : shapeChunk 6656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_7168 : shapeChunk 7168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_7680 : shapeChunk 7680 512 = true := by
  decide +kernel

theorem shapes_0 (n : Nat) (hlo : 0 ≤ n) (hhi : n < 8192) : shapeAt n = true := by
  by_cases h0 : n < 512
  · exact shapeChunk_sound shaped_0 n (by omega) h0
  by_cases h512 : n < 1024
  · exact shapeChunk_sound shaped_512 n (by omega) h512
  by_cases h1024 : n < 1536
  · exact shapeChunk_sound shaped_1024 n (by omega) h1024
  by_cases h1536 : n < 2048
  · exact shapeChunk_sound shaped_1536 n (by omega) h1536
  by_cases h2048 : n < 2560
  · exact shapeChunk_sound shaped_2048 n (by omega) h2048
  by_cases h2560 : n < 3072
  · exact shapeChunk_sound shaped_2560 n (by omega) h2560
  by_cases h3072 : n < 3584
  · exact shapeChunk_sound shaped_3072 n (by omega) h3072
  by_cases h3584 : n < 4096
  · exact shapeChunk_sound shaped_3584 n (by omega) h3584
  by_cases h4096 : n < 4608
  · exact shapeChunk_sound shaped_4096 n (by omega) h4096
  by_cases h4608 : n < 5120
  · exact shapeChunk_sound shaped_4608 n (by omega) h4608
  by_cases h5120 : n < 5632
  · exact shapeChunk_sound shaped_5120 n (by omega) h5120
  by_cases h5632 : n < 6144
  · exact shapeChunk_sound shaped_5632 n (by omega) h5632
  by_cases h6144 : n < 6656
  · exact shapeChunk_sound shaped_6144 n (by omega) h6144
  by_cases h6656 : n < 7168
  · exact shapeChunk_sound shaped_6656 n (by omega) h6656
  by_cases h7168 : n < 7680
  · exact shapeChunk_sound shaped_7168 n (by omega) h7168
  exact shapeChunk_sound shaped_7680 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
