module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Output

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem shaped_4096 : shapeChunk 4096 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_5120 : shapeChunk 5120 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_6144 : shapeChunk 6144 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_7168 : shapeChunk 7168 1024 = true := by
  decide +kernel


end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
