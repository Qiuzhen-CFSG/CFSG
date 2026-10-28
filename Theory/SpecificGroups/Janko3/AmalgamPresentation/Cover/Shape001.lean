module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_8192 : shapeChunk 8192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_8704 : shapeChunk 8704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_9216 : shapeChunk 9216 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_9728 : shapeChunk 9728 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_10240 : shapeChunk 10240 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_10752 : shapeChunk 10752 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_11264 : shapeChunk 11264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_11776 : shapeChunk 11776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_12288 : shapeChunk 12288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_12800 : shapeChunk 12800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_13312 : shapeChunk 13312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_13824 : shapeChunk 13824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_14336 : shapeChunk 14336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_14848 : shapeChunk 14848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_15360 : shapeChunk 15360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_15872 : shapeChunk 15872 512 = true := by
  decide +kernel

theorem shapes_8192 (n : Nat) (hlo : 8192 ≤ n) (hhi : n < 16384) : shapeAt n = true := by
  by_cases h8192 : n < 8704
  · exact shapeChunk_sound shaped_8192 n (by omega) h8192
  by_cases h8704 : n < 9216
  · exact shapeChunk_sound shaped_8704 n (by omega) h8704
  by_cases h9216 : n < 9728
  · exact shapeChunk_sound shaped_9216 n (by omega) h9216
  by_cases h9728 : n < 10240
  · exact shapeChunk_sound shaped_9728 n (by omega) h9728
  by_cases h10240 : n < 10752
  · exact shapeChunk_sound shaped_10240 n (by omega) h10240
  by_cases h10752 : n < 11264
  · exact shapeChunk_sound shaped_10752 n (by omega) h10752
  by_cases h11264 : n < 11776
  · exact shapeChunk_sound shaped_11264 n (by omega) h11264
  by_cases h11776 : n < 12288
  · exact shapeChunk_sound shaped_11776 n (by omega) h11776
  by_cases h12288 : n < 12800
  · exact shapeChunk_sound shaped_12288 n (by omega) h12288
  by_cases h12800 : n < 13312
  · exact shapeChunk_sound shaped_12800 n (by omega) h12800
  by_cases h13312 : n < 13824
  · exact shapeChunk_sound shaped_13312 n (by omega) h13312
  by_cases h13824 : n < 14336
  · exact shapeChunk_sound shaped_13824 n (by omega) h13824
  by_cases h14336 : n < 14848
  · exact shapeChunk_sound shaped_14336 n (by omega) h14336
  by_cases h14848 : n < 15360
  · exact shapeChunk_sound shaped_14848 n (by omega) h14848
  by_cases h15360 : n < 15872
  · exact shapeChunk_sound shaped_15360 n (by omega) h15360
  exact shapeChunk_sound shaped_15872 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
