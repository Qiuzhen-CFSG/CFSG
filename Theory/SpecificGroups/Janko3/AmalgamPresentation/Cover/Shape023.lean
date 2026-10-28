module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_188416 : shapeChunk 188416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_188928 : shapeChunk 188928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_189440 : shapeChunk 189440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_189952 : shapeChunk 189952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_190464 : shapeChunk 190464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_190976 : shapeChunk 190976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_191488 : shapeChunk 191488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_192000 : shapeChunk 192000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_192512 : shapeChunk 192512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_193024 : shapeChunk 193024 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_193536 : shapeChunk 193536 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_194048 : shapeChunk 194048 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_194560 : shapeChunk 194560 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_195072 : shapeChunk 195072 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_195584 : shapeChunk 195584 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_196096 : shapeChunk 196096 512 = true := by
  decide +kernel

theorem shapes_188416 (n : Nat) (hlo : 188416 ≤ n) (hhi : n < 196608) : shapeAt n = true := by
  by_cases h188416 : n < 188928
  · exact shapeChunk_sound shaped_188416 n (by omega) h188416
  by_cases h188928 : n < 189440
  · exact shapeChunk_sound shaped_188928 n (by omega) h188928
  by_cases h189440 : n < 189952
  · exact shapeChunk_sound shaped_189440 n (by omega) h189440
  by_cases h189952 : n < 190464
  · exact shapeChunk_sound shaped_189952 n (by omega) h189952
  by_cases h190464 : n < 190976
  · exact shapeChunk_sound shaped_190464 n (by omega) h190464
  by_cases h190976 : n < 191488
  · exact shapeChunk_sound shaped_190976 n (by omega) h190976
  by_cases h191488 : n < 192000
  · exact shapeChunk_sound shaped_191488 n (by omega) h191488
  by_cases h192000 : n < 192512
  · exact shapeChunk_sound shaped_192000 n (by omega) h192000
  by_cases h192512 : n < 193024
  · exact shapeChunk_sound shaped_192512 n (by omega) h192512
  by_cases h193024 : n < 193536
  · exact shapeChunk_sound shaped_193024 n (by omega) h193024
  by_cases h193536 : n < 194048
  · exact shapeChunk_sound shaped_193536 n (by omega) h193536
  by_cases h194048 : n < 194560
  · exact shapeChunk_sound shaped_194048 n (by omega) h194048
  by_cases h194560 : n < 195072
  · exact shapeChunk_sound shaped_194560 n (by omega) h194560
  by_cases h195072 : n < 195584
  · exact shapeChunk_sound shaped_195072 n (by omega) h195072
  by_cases h195584 : n < 196096
  · exact shapeChunk_sound shaped_195584 n (by omega) h195584
  exact shapeChunk_sound shaped_196096 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
