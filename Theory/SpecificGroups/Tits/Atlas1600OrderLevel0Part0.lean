module

public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Forward transition checks, part 1 of 4

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

private theorem checked0 : stepBatch 0 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked1 : stepBatch 4 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked2 : stepBatch 8 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked3 : stepBatch 12 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked4 : stepBatch 16 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked5 : stepBatch 20 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked6 : stepBatch 24 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked7 : stepBatch 28 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked8 : stepBatch 32 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked9 : stepBatch 36 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked10 : stepBatch 40 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked11 : stepBatch 44 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked12 : stepBatch 48 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked13 : stepBatch 52 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked14 : stepBatch 56 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked15 : stepBatch 60 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked16 : stepBatch 64 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked17 : stepBatch 68 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked18 : stepBatch 72 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

private theorem checked19 : stepBatch 76 := by
  apply ofStepBatchCheck
  apply allFin₂
  decide +kernel

public theorem part0 (b : Fin 20) : stepBatch ⟨4 * b.val + 0, by omega⟩ := by
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
