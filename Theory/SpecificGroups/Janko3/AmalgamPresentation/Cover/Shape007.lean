module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_57344 : shapeChunk 57344 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_57856 : shapeChunk 57856 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_58368 : shapeChunk 58368 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_58880 : shapeChunk 58880 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_59392 : shapeChunk 59392 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_59904 : shapeChunk 59904 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_60416 : shapeChunk 60416 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_60928 : shapeChunk 60928 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_61440 : shapeChunk 61440 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_61952 : shapeChunk 61952 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_62464 : shapeChunk 62464 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_62976 : shapeChunk 62976 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_63488 : shapeChunk 63488 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_64000 : shapeChunk 64000 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_64512 : shapeChunk 64512 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem shaped_65024 : shapeChunk 65024 512 = true := by
  decide +kernel

theorem shapes_57344 (n : Nat) (hlo : 57344 ≤ n) (hhi : n < 65536) : shapeAt n = true := by
  by_cases h57344 : n < 57856
  · exact shapeChunk_sound shaped_57344 n (by omega) h57344
  by_cases h57856 : n < 58368
  · exact shapeChunk_sound shaped_57856 n (by omega) h57856
  by_cases h58368 : n < 58880
  · exact shapeChunk_sound shaped_58368 n (by omega) h58368
  by_cases h58880 : n < 59392
  · exact shapeChunk_sound shaped_58880 n (by omega) h58880
  by_cases h59392 : n < 59904
  · exact shapeChunk_sound shaped_59392 n (by omega) h59392
  by_cases h59904 : n < 60416
  · exact shapeChunk_sound shaped_59904 n (by omega) h59904
  by_cases h60416 : n < 60928
  · exact shapeChunk_sound shaped_60416 n (by omega) h60416
  by_cases h60928 : n < 61440
  · exact shapeChunk_sound shaped_60928 n (by omega) h60928
  by_cases h61440 : n < 61952
  · exact shapeChunk_sound shaped_61440 n (by omega) h61440
  by_cases h61952 : n < 62464
  · exact shapeChunk_sound shaped_61952 n (by omega) h61952
  by_cases h62464 : n < 62976
  · exact shapeChunk_sound shaped_62464 n (by omega) h62464
  by_cases h62976 : n < 63488
  · exact shapeChunk_sound shaped_62976 n (by omega) h62976
  by_cases h63488 : n < 64000
  · exact shapeChunk_sound shaped_63488 n (by omega) h63488
  by_cases h64000 : n < 64512
  · exact shapeChunk_sound shaped_64000 n (by omega) h64000
  by_cases h64512 : n < 65024
  · exact shapeChunk_sound shaped_64512 n (by omega) h64512
  exact shapeChunk_sound shaped_65024 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
