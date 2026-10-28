module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_98304 : shapeChunk 98304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_98816 : shapeChunk 98816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_99328 : shapeChunk 99328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_99840 : shapeChunk 99840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_100352 : shapeChunk 100352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_100864 : shapeChunk 100864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_101376 : shapeChunk 101376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_101888 : shapeChunk 101888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_102400 : shapeChunk 102400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_102912 : shapeChunk 102912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_103424 : shapeChunk 103424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_103936 : shapeChunk 103936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_104448 : shapeChunk 104448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_104960 : shapeChunk 104960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_105472 : shapeChunk 105472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_105984 : shapeChunk 105984 512 = true := by
  decide +kernel

theorem shapes_98304 (n : Nat) (hlo : 98304 ≤ n) (hhi : n < 106496) : shapeAt n = true := by
  by_cases h98304 : n < 98816
  · exact shapeChunk_sound shaped_98304 n (by omega) h98304
  by_cases h98816 : n < 99328
  · exact shapeChunk_sound shaped_98816 n (by omega) h98816
  by_cases h99328 : n < 99840
  · exact shapeChunk_sound shaped_99328 n (by omega) h99328
  by_cases h99840 : n < 100352
  · exact shapeChunk_sound shaped_99840 n (by omega) h99840
  by_cases h100352 : n < 100864
  · exact shapeChunk_sound shaped_100352 n (by omega) h100352
  by_cases h100864 : n < 101376
  · exact shapeChunk_sound shaped_100864 n (by omega) h100864
  by_cases h101376 : n < 101888
  · exact shapeChunk_sound shaped_101376 n (by omega) h101376
  by_cases h101888 : n < 102400
  · exact shapeChunk_sound shaped_101888 n (by omega) h101888
  by_cases h102400 : n < 102912
  · exact shapeChunk_sound shaped_102400 n (by omega) h102400
  by_cases h102912 : n < 103424
  · exact shapeChunk_sound shaped_102912 n (by omega) h102912
  by_cases h103424 : n < 103936
  · exact shapeChunk_sound shaped_103424 n (by omega) h103424
  by_cases h103936 : n < 104448
  · exact shapeChunk_sound shaped_103936 n (by omega) h103936
  by_cases h104448 : n < 104960
  · exact shapeChunk_sound shaped_104448 n (by omega) h104448
  by_cases h104960 : n < 105472
  · exact shapeChunk_sound shaped_104960 n (by omega) h104960
  by_cases h105472 : n < 105984
  · exact shapeChunk_sound shaped_105472 n (by omega) h105472
  exact shapeChunk_sound shaped_105984 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
