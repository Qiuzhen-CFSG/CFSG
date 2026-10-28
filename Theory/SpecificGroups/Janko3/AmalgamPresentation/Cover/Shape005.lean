module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_40960 : shapeChunk 40960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_41472 : shapeChunk 41472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_41984 : shapeChunk 41984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_42496 : shapeChunk 42496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_43008 : shapeChunk 43008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_43520 : shapeChunk 43520 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_44032 : shapeChunk 44032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_44544 : shapeChunk 44544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_45056 : shapeChunk 45056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_45568 : shapeChunk 45568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_46080 : shapeChunk 46080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_46592 : shapeChunk 46592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_47104 : shapeChunk 47104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_47616 : shapeChunk 47616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_48128 : shapeChunk 48128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_48640 : shapeChunk 48640 512 = true := by
  decide +kernel

theorem shapes_40960 (n : Nat) (hlo : 40960 ≤ n) (hhi : n < 49152) : shapeAt n = true := by
  by_cases h40960 : n < 41472
  · exact shapeChunk_sound shaped_40960 n (by omega) h40960
  by_cases h41472 : n < 41984
  · exact shapeChunk_sound shaped_41472 n (by omega) h41472
  by_cases h41984 : n < 42496
  · exact shapeChunk_sound shaped_41984 n (by omega) h41984
  by_cases h42496 : n < 43008
  · exact shapeChunk_sound shaped_42496 n (by omega) h42496
  by_cases h43008 : n < 43520
  · exact shapeChunk_sound shaped_43008 n (by omega) h43008
  by_cases h43520 : n < 44032
  · exact shapeChunk_sound shaped_43520 n (by omega) h43520
  by_cases h44032 : n < 44544
  · exact shapeChunk_sound shaped_44032 n (by omega) h44032
  by_cases h44544 : n < 45056
  · exact shapeChunk_sound shaped_44544 n (by omega) h44544
  by_cases h45056 : n < 45568
  · exact shapeChunk_sound shaped_45056 n (by omega) h45056
  by_cases h45568 : n < 46080
  · exact shapeChunk_sound shaped_45568 n (by omega) h45568
  by_cases h46080 : n < 46592
  · exact shapeChunk_sound shaped_46080 n (by omega) h46080
  by_cases h46592 : n < 47104
  · exact shapeChunk_sound shaped_46592 n (by omega) h46592
  by_cases h47104 : n < 47616
  · exact shapeChunk_sound shaped_47104 n (by omega) h47104
  by_cases h47616 : n < 48128
  · exact shapeChunk_sound shaped_47616 n (by omega) h47616
  by_cases h48128 : n < 48640
  · exact shapeChunk_sound shaped_48128 n (by omega) h48128
  exact shapeChunk_sound shaped_48640 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
