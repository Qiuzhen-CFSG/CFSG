module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Output

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem shaped_0 : shapeChunk 0 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_1024 : shapeChunk 1024 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_2048 : shapeChunk 2048 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_3072 : shapeChunk 3072 1024 = true := by
  decide +kernel


end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
