module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_32768 : shapeChunk 32768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_33280 : shapeChunk 33280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_33792 : shapeChunk 33792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_34304 : shapeChunk 34304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_34816 : shapeChunk 34816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_35328 : shapeChunk 35328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_35840 : shapeChunk 35840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_36352 : shapeChunk 36352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_36864 : shapeChunk 36864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_37376 : shapeChunk 37376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_37888 : shapeChunk 37888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_38400 : shapeChunk 38400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_38912 : shapeChunk 38912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_39424 : shapeChunk 39424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_39936 : shapeChunk 39936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_40448 : shapeChunk 40448 512 = true := by
  decide +kernel

theorem shapes_32768 (n : Nat) (hlo : 32768 ≤ n) (hhi : n < 40960) : shapeAt n = true := by
  by_cases h32768 : n < 33280
  · exact shapeChunk_sound shaped_32768 n (by omega) h32768
  by_cases h33280 : n < 33792
  · exact shapeChunk_sound shaped_33280 n (by omega) h33280
  by_cases h33792 : n < 34304
  · exact shapeChunk_sound shaped_33792 n (by omega) h33792
  by_cases h34304 : n < 34816
  · exact shapeChunk_sound shaped_34304 n (by omega) h34304
  by_cases h34816 : n < 35328
  · exact shapeChunk_sound shaped_34816 n (by omega) h34816
  by_cases h35328 : n < 35840
  · exact shapeChunk_sound shaped_35328 n (by omega) h35328
  by_cases h35840 : n < 36352
  · exact shapeChunk_sound shaped_35840 n (by omega) h35840
  by_cases h36352 : n < 36864
  · exact shapeChunk_sound shaped_36352 n (by omega) h36352
  by_cases h36864 : n < 37376
  · exact shapeChunk_sound shaped_36864 n (by omega) h36864
  by_cases h37376 : n < 37888
  · exact shapeChunk_sound shaped_37376 n (by omega) h37376
  by_cases h37888 : n < 38400
  · exact shapeChunk_sound shaped_37888 n (by omega) h37888
  by_cases h38400 : n < 38912
  · exact shapeChunk_sound shaped_38400 n (by omega) h38400
  by_cases h38912 : n < 39424
  · exact shapeChunk_sound shaped_38912 n (by omega) h38912
  by_cases h39424 : n < 39936
  · exact shapeChunk_sound shaped_39424 n (by omega) h39424
  by_cases h39936 : n < 40448
  · exact shapeChunk_sound shaped_39936 n (by omega) h39936
  exact shapeChunk_sound shaped_40448 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
