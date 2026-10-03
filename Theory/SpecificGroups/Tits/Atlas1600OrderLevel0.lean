module

public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Part0
public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Part1
public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Part2
public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Part3
import Mathlib.Tactic.FinCases

/-!
# The 1600-point stabilizer-chain step in the Atlas degree-1600 model

The imported certificates check the two forward generators on all 1600 word
representatives. Word reduction proves most transitions, and the kernel checks
the remaining pointwise identities. The inverse transitions follow from the
generator orders 2 and 3. The word-subgroup bijection then gives index 1600.

The witnesses originate from
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits.Atlas1600OrderCertificate
open Theory.GroupTheory ForwardReduction

private theorem checkedPart (k : Fin 4) (b : Fin 20) :
    stepBatch ⟨4 * b.val + k.val, by omega⟩ := by
  fin_cases k
  · exact part0 b
  · exact part1 b
  · exact part2 b
  · exact part3 b

private theorem checkedBatch (b : Fin 80) : stepBatch b := by
  let k : Fin 4 := ⟨b.val % 4, by omega⟩
  let q : Fin 20 := ⟨b.val / 4, by omega⟩
  have hb : (⟨4 * q.val + k.val, by omega⟩ : Fin 80) = b := by
    apply Fin.ext
    dsimp [k, q]
    omega
  simpa only [hb] using checkedPart k q

private theorem positiveStep (i : Fin 2) (r : Fin 1600) :
    L0Gen (i.castLE (by decide)) * L0Rep r =
      L0Rep (L0Act (i.castLE (by decide)) r) * evalWord L1Gen (L0Factor (i.castLE (by decide)) r) := by
  let b : Fin 80 := ⟨r.val / 20, by omega⟩
  let s : Fin 20 := ⟨r.val % 20, by omega⟩
  have hrs : batchRep b s = r := by
    apply Fin.ext
    dsimp [batchRep, b, s]
    omega
  simpa only [hrs] using checkedBatch b i s

/-- The first stabilizer-chain index is 1600. -/
public theorem H0_card_step : Nat.card H0 = 1600 * Nat.card H1 :=
  card_step_of_positive positiveStep

end Tits.Atlas1600OrderCertificate
