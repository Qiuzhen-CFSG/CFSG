module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_172032 : shapeChunk 172032 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_172544 : shapeChunk 172544 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_173056 : shapeChunk 173056 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_173568 : shapeChunk 173568 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_174080 : shapeChunk 174080 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_174592 : shapeChunk 174592 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_175104 : shapeChunk 175104 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_175616 : shapeChunk 175616 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_176128 : shapeChunk 176128 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_176640 : shapeChunk 176640 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_177152 : shapeChunk 177152 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_177664 : shapeChunk 177664 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_178176 : shapeChunk 178176 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_178688 : shapeChunk 178688 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_179200 : shapeChunk 179200 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_179712 : shapeChunk 179712 512 = true := by
  decide +kernel

theorem shapes_172032 (n : Nat) (hlo : 172032 ≤ n) (hhi : n < 180224) : shapeAt n = true := by
  by_cases h172032 : n < 172544
  · exact shapeChunk_sound shaped_172032 n (by omega) h172032
  by_cases h172544 : n < 173056
  · exact shapeChunk_sound shaped_172544 n (by omega) h172544
  by_cases h173056 : n < 173568
  · exact shapeChunk_sound shaped_173056 n (by omega) h173056
  by_cases h173568 : n < 174080
  · exact shapeChunk_sound shaped_173568 n (by omega) h173568
  by_cases h174080 : n < 174592
  · exact shapeChunk_sound shaped_174080 n (by omega) h174080
  by_cases h174592 : n < 175104
  · exact shapeChunk_sound shaped_174592 n (by omega) h174592
  by_cases h175104 : n < 175616
  · exact shapeChunk_sound shaped_175104 n (by omega) h175104
  by_cases h175616 : n < 176128
  · exact shapeChunk_sound shaped_175616 n (by omega) h175616
  by_cases h176128 : n < 176640
  · exact shapeChunk_sound shaped_176128 n (by omega) h176128
  by_cases h176640 : n < 177152
  · exact shapeChunk_sound shaped_176640 n (by omega) h176640
  by_cases h177152 : n < 177664
  · exact shapeChunk_sound shaped_177152 n (by omega) h177152
  by_cases h177664 : n < 178176
  · exact shapeChunk_sound shaped_177664 n (by omega) h177664
  by_cases h178176 : n < 178688
  · exact shapeChunk_sound shaped_178176 n (by omega) h178176
  by_cases h178688 : n < 179200
  · exact shapeChunk_sound shaped_178688 n (by omega) h178688
  by_cases h179200 : n < 179712
  · exact shapeChunk_sound shaped_179200 n (by omega) h179200
  exact shapeChunk_sound shaped_179712 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
