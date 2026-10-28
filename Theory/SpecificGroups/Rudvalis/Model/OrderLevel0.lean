module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Data
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6
import Mathlib.Tactic.FinCases

/-!
# The first Rudvalis stabilizer-chain index

The seven independently checked parts certify the two forward generators on
all 4060 representatives. Inverse transitions follow from the generator orders
2 and 4, and the transversal bijection gives index 4060 for the fixed subgroups
in `OrderChainData`.

Witness source: the ATLAS degree-4060 permutations and the word witnesses
documented in `OrderCertificate/GenerateChain.g`. The imported certificates
check their identities in Lean's kernel.
-/

namespace Rudvalis.OrderCertificate
open ForwardReduction

private theorem checkedPart (k : Fin 7) (b : Fin 29) :
    stepBatch ⟨7 * b.val + k.val, by omega⟩ := by
  fin_cases k
  · exact part0 b
  · exact part1 b
  · exact part2 b
  · exact part3 b
  · exact part4 b
  · exact part5 b
  · exact part6 b

/-- The index of the first fixed word subgroup in the Rudvalis model is 4060. -/
public theorem H0_card_step : Nat.card H0 = 4060 * Nat.card H1 :=
  card_step_of_parts checkedPart

end Rudvalis.OrderCertificate
