module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.Output

/-! Kernel-checked deductions for the literal ATLAS J3G1-P1 subgroup M₁.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem shaped_12288 : shapeChunk 12288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_13312 : shapeChunk 13312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_14336 : shapeChunk 14336 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_15360 : shapeChunk 15360 1024 = true := by
  decide +kernel


end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
