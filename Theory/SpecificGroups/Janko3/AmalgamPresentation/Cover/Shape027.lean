module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Output

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem shaped_221184 : shapeChunk 221184 432 = true := by
  decide +kernel

theorem shapes_221184 (n : Nat) (hlo : 221184 ≤ n) (hhi : n < 221616) : shapeAt n = true := by
  exact shapeChunk_sound shaped_221184 n (by omega) hhi

end Sporadic.Janko3.AmalgamPresentation.Cover
