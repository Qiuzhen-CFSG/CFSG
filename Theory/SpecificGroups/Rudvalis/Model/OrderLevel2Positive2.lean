module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Block7

import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator-2 transition certificate

The 256 bounded batch certificates cover all 1024 representatives.  Their
pointwise permutation identities and cancellation reductions are checked by
Lean's kernel.

Source: the ATLAS degree-4060 witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2
open Theory.GroupTheory Level2Reduction

/-- The third forward generator transitions every level-2 representative. -/
public theorem positiveStep (r : Fin 1024) :
    L2Gen 2 * L2Rep r = L2Rep (L2Act 2 r) * evalWord L3Gen (L2Factor 2 r) := by
  apply positiveStep_of_batches 2
  have h : ∀ (k : Fin 8) (s : Fin 32),
      stepBatch 2 ⟨32 * k.val + s.val, by omega⟩ := by
    intro k
    fin_cases k
    · exact Block0.batches
    · exact Block1.batches
    · exact Block2.batches
    · exact Block3.batches
    · exact Block4.batches
    · exact Block5.batches
    · exact Block6.batches
    · exact Block7.batches
  intro b
  let k : Fin 8 := ⟨b.val / 32, by omega⟩
  let s : Fin 32 := ⟨b.val % 32, by omega⟩
  have hbs : (⟨32 * k.val + s.val, by omega⟩ : Fin 256) = b := by
    apply Fin.ext
    dsimp [k, s]
    omega
  simpa only [hbs] using h k s

end Rudvalis.OrderCertificate.OrderLevel2Positive2
