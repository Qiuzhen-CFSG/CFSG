module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_163840 : shapeChunk 163840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_164352 : shapeChunk 164352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_164864 : shapeChunk 164864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_165376 : shapeChunk 165376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_165888 : shapeChunk 165888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_166400 : shapeChunk 166400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_166912 : shapeChunk 166912 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_167424 : shapeChunk 167424 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_167936 : shapeChunk 167936 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_168448 : shapeChunk 168448 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_168960 : shapeChunk 168960 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_169472 : shapeChunk 169472 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_169984 : shapeChunk 169984 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_170496 : shapeChunk 170496 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_171008 : shapeChunk 171008 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_171520 : shapeChunk 171520 512 = true := by
  decide +kernel

theorem shapes_163840 (n : Nat) (hlo : 163840 ≤ n) (hhi : n < 172032) : shapeAt n = true := by
  by_cases h163840 : n < 164352
  · exact shapeChunk_sound shaped_163840 n (by omega) h163840
  by_cases h164352 : n < 164864
  · exact shapeChunk_sound shaped_164352 n (by omega) h164352
  by_cases h164864 : n < 165376
  · exact shapeChunk_sound shaped_164864 n (by omega) h164864
  by_cases h165376 : n < 165888
  · exact shapeChunk_sound shaped_165376 n (by omega) h165376
  by_cases h165888 : n < 166400
  · exact shapeChunk_sound shaped_165888 n (by omega) h165888
  by_cases h166400 : n < 166912
  · exact shapeChunk_sound shaped_166400 n (by omega) h166400
  by_cases h166912 : n < 167424
  · exact shapeChunk_sound shaped_166912 n (by omega) h166912
  by_cases h167424 : n < 167936
  · exact shapeChunk_sound shaped_167424 n (by omega) h167424
  by_cases h167936 : n < 168448
  · exact shapeChunk_sound shaped_167936 n (by omega) h167936
  by_cases h168448 : n < 168960
  · exact shapeChunk_sound shaped_168448 n (by omega) h168448
  by_cases h168960 : n < 169472
  · exact shapeChunk_sound shaped_168960 n (by omega) h168960
  by_cases h169472 : n < 169984
  · exact shapeChunk_sound shaped_169472 n (by omega) h169472
  by_cases h169984 : n < 170496
  · exact shapeChunk_sound shaped_169984 n (by omega) h169984
  by_cases h170496 : n < 171008
  · exact shapeChunk_sound shaped_170496 n (by omega) h170496
  by_cases h171008 : n < 171520
  · exact shapeChunk_sound shaped_171008 n (by omega) h171008
  exact shapeChunk_sound shaped_171520 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
