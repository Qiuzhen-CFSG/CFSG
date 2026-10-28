module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Output

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem shaped_8192 : shapeChunk 8192 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_9216 : shapeChunk 9216 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_10240 : shapeChunk 10240 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_11264 : shapeChunk 11264 1024 = true := by
  decide +kernel


end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
