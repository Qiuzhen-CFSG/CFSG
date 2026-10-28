module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Output

/-! Kernel-checked deductions for the literal normalized J₂ centralizer presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
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

set_option maxRecDepth 4096 in
theorem shaped_12288 : shapeChunk 12288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_13312 : shapeChunk 13312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem shaped_14336 : shapeChunk 14336 1024 = true := by
  decide +kernel


end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
