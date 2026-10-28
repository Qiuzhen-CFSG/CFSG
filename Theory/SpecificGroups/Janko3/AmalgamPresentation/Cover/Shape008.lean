module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_65536 : shapeChunk 65536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_66048 : shapeChunk 66048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_66560 : shapeChunk 66560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_67072 : shapeChunk 67072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_67584 : shapeChunk 67584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_68096 : shapeChunk 68096 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_68608 : shapeChunk 68608 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_69120 : shapeChunk 69120 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_69632 : shapeChunk 69632 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_70144 : shapeChunk 70144 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_70656 : shapeChunk 70656 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_71168 : shapeChunk 71168 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_71680 : shapeChunk 71680 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_72192 : shapeChunk 72192 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_72704 : shapeChunk 72704 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_73216 : shapeChunk 73216 512 = true := by
  decide +kernel

theorem shapes_65536 (n : Nat) (hlo : 65536 ≤ n) (hhi : n < 73728) : shapeAt n = true := by
  by_cases h65536 : n < 66048
  · exact shapeChunk_sound shaped_65536 n (by omega) h65536
  by_cases h66048 : n < 66560
  · exact shapeChunk_sound shaped_66048 n (by omega) h66048
  by_cases h66560 : n < 67072
  · exact shapeChunk_sound shaped_66560 n (by omega) h66560
  by_cases h67072 : n < 67584
  · exact shapeChunk_sound shaped_67072 n (by omega) h67072
  by_cases h67584 : n < 68096
  · exact shapeChunk_sound shaped_67584 n (by omega) h67584
  by_cases h68096 : n < 68608
  · exact shapeChunk_sound shaped_68096 n (by omega) h68096
  by_cases h68608 : n < 69120
  · exact shapeChunk_sound shaped_68608 n (by omega) h68608
  by_cases h69120 : n < 69632
  · exact shapeChunk_sound shaped_69120 n (by omega) h69120
  by_cases h69632 : n < 70144
  · exact shapeChunk_sound shaped_69632 n (by omega) h69632
  by_cases h70144 : n < 70656
  · exact shapeChunk_sound shaped_70144 n (by omega) h70144
  by_cases h70656 : n < 71168
  · exact shapeChunk_sound shaped_70656 n (by omega) h70656
  by_cases h71168 : n < 71680
  · exact shapeChunk_sound shaped_71168 n (by omega) h71168
  by_cases h71680 : n < 72192
  · exact shapeChunk_sound shaped_71680 n (by omega) h71680
  by_cases h72192 : n < 72704
  · exact shapeChunk_sound shaped_72192 n (by omega) h72192
  by_cases h72704 : n < 73216
  · exact shapeChunk_sound shaped_72704 n (by omega) h72704
  exact shapeChunk_sound shaped_73216 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
