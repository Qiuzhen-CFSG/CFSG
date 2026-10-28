module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Output

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem shaped_16384 : shapeChunk 16384 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_17408 : shapeChunk 17408 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_18432 : shapeChunk 18432 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_19456 : shapeChunk 19456 1024 = true := by
  decide +kernel


end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
