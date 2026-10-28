module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_90112 : shapeChunk 90112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_90624 : shapeChunk 90624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_91136 : shapeChunk 91136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_91648 : shapeChunk 91648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_92160 : shapeChunk 92160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_92672 : shapeChunk 92672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_93184 : shapeChunk 93184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_93696 : shapeChunk 93696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_94208 : shapeChunk 94208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_94720 : shapeChunk 94720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_95232 : shapeChunk 95232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_95744 : shapeChunk 95744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_96256 : shapeChunk 96256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_96768 : shapeChunk 96768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_97280 : shapeChunk 97280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_97792 : shapeChunk 97792 512 = true := by
  decide +kernel

theorem shapes_90112 (n : Nat) (hlo : 90112 ≤ n) (hhi : n < 98304) : shapeAt n = true := by
  by_cases h90112 : n < 90624
  · exact shapeChunk_sound shaped_90112 n (by omega) h90112
  by_cases h90624 : n < 91136
  · exact shapeChunk_sound shaped_90624 n (by omega) h90624
  by_cases h91136 : n < 91648
  · exact shapeChunk_sound shaped_91136 n (by omega) h91136
  by_cases h91648 : n < 92160
  · exact shapeChunk_sound shaped_91648 n (by omega) h91648
  by_cases h92160 : n < 92672
  · exact shapeChunk_sound shaped_92160 n (by omega) h92160
  by_cases h92672 : n < 93184
  · exact shapeChunk_sound shaped_92672 n (by omega) h92672
  by_cases h93184 : n < 93696
  · exact shapeChunk_sound shaped_93184 n (by omega) h93184
  by_cases h93696 : n < 94208
  · exact shapeChunk_sound shaped_93696 n (by omega) h93696
  by_cases h94208 : n < 94720
  · exact shapeChunk_sound shaped_94208 n (by omega) h94208
  by_cases h94720 : n < 95232
  · exact shapeChunk_sound shaped_94720 n (by omega) h94720
  by_cases h95232 : n < 95744
  · exact shapeChunk_sound shaped_95232 n (by omega) h95232
  by_cases h95744 : n < 96256
  · exact shapeChunk_sound shaped_95744 n (by omega) h95744
  by_cases h96256 : n < 96768
  · exact shapeChunk_sound shaped_96256 n (by omega) h96256
  by_cases h96768 : n < 97280
  · exact shapeChunk_sound shaped_96768 n (by omega) h96768
  by_cases h97280 : n < 97792
  · exact shapeChunk_sound shaped_97280 n (by omega) h97280
  exact shapeChunk_sound shaped_97792 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
