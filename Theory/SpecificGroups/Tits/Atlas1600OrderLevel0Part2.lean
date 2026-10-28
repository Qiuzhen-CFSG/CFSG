module

public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Forward transition checks, part 3 of 4

This checks every fourth batch of 20 representatives, using the word reduction
checker and its soundness theorem. The remaining permutation identities are
checked pointwise by the kernel. Sequential batches bound memory, and the four
parts can be built independently. The witnesses originate from
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits.Atlas1600OrderCertificate.ForwardReduction
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option Elab.async false

private theorem checked0 : stepBatch 2 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked1 : stepBatch 6 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked2 : stepBatch 10 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked3 : stepBatch 14 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked4 : stepBatch 18 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked5 : stepBatch 22 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked6 : stepBatch 26 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked7 : stepBatch 30 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked8 : stepBatch 34 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked9 : stepBatch 38 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked10 : stepBatch 42 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked11 : stepBatch 46 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked12 : stepBatch 50 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked13 : stepBatch 54 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked14 : stepBatch 58 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked15 : stepBatch 62 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked16 : stepBatch 66 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked17 : stepBatch 70 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked18 : stepBatch 74 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked19 : stepBatch 78 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

public theorem part2 (b : Fin 20) : stepBatch ⟨4 * b.val + 2, by omega⟩ := by
  fin_cases b
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19

end Tits.Atlas1600OrderCertificate.ForwardReduction
