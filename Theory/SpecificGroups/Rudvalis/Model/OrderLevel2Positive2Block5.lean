module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block5Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block5Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block5Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block5Part3

import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 160–191

Four smaller modules kernel-check eight batches each. Splitting this range
bounds compilation cost while preserving the 32-batch interface.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5
open Level2Reduction

/-- The thirty-two batches from 160 through 191. -/
public theorem batches (b : Fin 32) : stepBatch 2 ⟨160 + b.val, by omega⟩ := by
  have h : ∀ (k : Fin 4) (s : Fin 8),
      stepBatch 2 ⟨160 + 8 * k.val + s.val, by omega⟩ := by
    intro k
    fin_cases k
    · exact Part0.batches
    · exact Part1.batches
    · exact Part2.batches
    · exact Part3.batches
  let k : Fin 4 := ⟨b.val / 8, by omega⟩
  let s : Fin 8 := ⟨b.val % 8, by omega⟩
  have he : (⟨160 + 8 * k.val + s.val, by omega⟩ : Fin 256) =
      ⟨160 + b.val, by omega⟩ := by
    apply Fin.ext
    dsimp [k, s]
    omega
  simpa only [he] using h k s

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5
