module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_122880 : shapeChunk 122880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_123392 : shapeChunk 123392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_123904 : shapeChunk 123904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_124416 : shapeChunk 124416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_124928 : shapeChunk 124928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_125440 : shapeChunk 125440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_125952 : shapeChunk 125952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_126464 : shapeChunk 126464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_126976 : shapeChunk 126976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_127488 : shapeChunk 127488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_128000 : shapeChunk 128000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_128512 : shapeChunk 128512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_129024 : shapeChunk 129024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_129536 : shapeChunk 129536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_130048 : shapeChunk 130048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_130560 : shapeChunk 130560 512 = true := by
  decide +kernel

theorem shapes_122880 (n : Nat) (hlo : 122880 ≤ n) (hhi : n < 131072) : shapeAt n = true := by
  by_cases h122880 : n < 123392
  · exact shapeChunk_sound shaped_122880 n (by omega) h122880
  by_cases h123392 : n < 123904
  · exact shapeChunk_sound shaped_123392 n (by omega) h123392
  by_cases h123904 : n < 124416
  · exact shapeChunk_sound shaped_123904 n (by omega) h123904
  by_cases h124416 : n < 124928
  · exact shapeChunk_sound shaped_124416 n (by omega) h124416
  by_cases h124928 : n < 125440
  · exact shapeChunk_sound shaped_124928 n (by omega) h124928
  by_cases h125440 : n < 125952
  · exact shapeChunk_sound shaped_125440 n (by omega) h125440
  by_cases h125952 : n < 126464
  · exact shapeChunk_sound shaped_125952 n (by omega) h125952
  by_cases h126464 : n < 126976
  · exact shapeChunk_sound shaped_126464 n (by omega) h126464
  by_cases h126976 : n < 127488
  · exact shapeChunk_sound shaped_126976 n (by omega) h126976
  by_cases h127488 : n < 128000
  · exact shapeChunk_sound shaped_127488 n (by omega) h127488
  by_cases h128000 : n < 128512
  · exact shapeChunk_sound shaped_128000 n (by omega) h128000
  by_cases h128512 : n < 129024
  · exact shapeChunk_sound shaped_128512 n (by omega) h128512
  by_cases h129024 : n < 129536
  · exact shapeChunk_sound shaped_129024 n (by omega) h129024
  by_cases h129536 : n < 130048
  · exact shapeChunk_sound shaped_129536 n (by omega) h129536
  by_cases h130048 : n < 130560
  · exact shapeChunk_sound shaped_130048 n (by omega) h130048
  exact shapeChunk_sound shaped_130560 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
