module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block7
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block8
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block9
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block14
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0Block15

import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 forward transition for generator 0

The 1024 representatives are partitioned into 256 batches of four.
Sixteen independently checked ranges supply all batches; the reduction
module converts their certificates to the required permutation identities.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive0
open Level2Reduction Theory.GroupTheory

/-- Every level-2 representative satisfies the generator-0 transition. -/
public theorem positiveStep (r : Fin 1024) :
    L2Gen 0 * L2Rep r = L2Rep (L2Act 0 r) * evalWord L3Gen (L2Factor 0 r) := by
  apply positiveStep_of_batches 0
  have h : ∀ (k : Fin 16) (s : Fin 16),
      stepBatch 0 ⟨16 * k.val + s.val, by omega⟩ := by
    intro k
    fin_cases k
    · exact block0
    · exact block1
    · exact block2
    · exact block3
    · exact block4
    · exact block5
    · exact block6
    · exact block7
    · exact block8
    · exact block9
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
  intro b
  let k : Fin 16 := ⟨b.val / 16, by omega⟩
  let s : Fin 16 := ⟨b.val % 16, by omega⟩
  have he : (⟨16 * k.val + s.val, by omega⟩ : Fin 256) = b := by
    apply Fin.ext
    dsimp [k, s]
    omega
  simpa only [he] using h k s

end Rudvalis.OrderCertificate.OrderLevel2Positive0
