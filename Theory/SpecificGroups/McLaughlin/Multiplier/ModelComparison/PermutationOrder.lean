module

public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Level0
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Level1
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Level2
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Level3
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Level4
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Level5

/-!
# A checked lower bound for the literal McL permutation carrier

The six prefixes of the base `[0, 1, 2, 3, 4, 5]` have certified orbit
representatives of sizes 275, 112, 81, 36, 5 and 2. Multiplication embeds
each representative family times the next point stabilizer into the previous
one. Their product gives 898128000 distinct elements of the subgroup generated
by the original `McLG1-p275B0` pair.

All auxiliary permutations have kernel-checked word expressions in that pair.
No assertion about a counted overgroup, a full Schreier chain, simplicity,
or the separate Leech model is used. This supplies the cardinality premise
of `ModelComparison.carrierEmbedding_bijective`; the generator lifts remain
with their independent owner.

Source: the ATLAS degree-275 McL representation and the exact cycle
transcription in `Theory/SpecificGroups/LeechRelated/AtlasCarriers/McL.lean`.
Discovery data and the reproducible formatter are retained in `source/`.
-/

namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open PermutationOrder

/-- The subgroup of the two literal ATLAS permutations has at least the
McLaughlin order. Every element counted is certified in that subgroup. -/
public theorem permutation_order_lower :
    898128000 ≤ Nat.card Sporadic.LeechRelated.McL.Carrier := by
  have h6 : 1 ≤ Nat.card (stabilizer 6) := Nat.card_pos
  have h5 : 2 ≤ Nat.card (stabilizer 5) := by
    calc
      2 = 2 * 1 := by decide
      _ ≤ 2 * Nat.card (stabilizer 6) := Nat.mul_le_mul_left _ h6
      _ ≤ Nat.card (stabilizer 5) := Level5.card_step
  have h4 : 10 ≤ Nat.card (stabilizer 4) := by
    calc
      10 = 5 * 2 := by decide
      _ ≤ 5 * Nat.card (stabilizer 5) := Nat.mul_le_mul_left _ h5
      _ ≤ Nat.card (stabilizer 4) := Level4.card_step
  have h3 : 360 ≤ Nat.card (stabilizer 3) := by
    calc
      360 = 36 * 10 := by decide
      _ ≤ 36 * Nat.card (stabilizer 4) := Nat.mul_le_mul_left _ h4
      _ ≤ Nat.card (stabilizer 3) := Level3.card_step
  have h2 : 29160 ≤ Nat.card (stabilizer 2) := by
    calc
      29160 = 81 * 360 := by decide
      _ ≤ 81 * Nat.card (stabilizer 3) := Nat.mul_le_mul_left _ h3
      _ ≤ Nat.card (stabilizer 2) := Level2.card_step
  have h1 : 3265920 ≤ Nat.card (stabilizer 1) := by
    calc
      3265920 = 112 * 29160 := by decide
      _ ≤ 112 * Nat.card (stabilizer 2) := Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card (stabilizer 1) := Level1.card_step
  change 898128000 ≤ Nat.card Sporadic.LeechRelated.McL.generated
  rw [← stabilizer_zero]
  calc
    898128000 = 275 * 3265920 := by decide
    _ ≤ 275 * Nat.card (stabilizer 1) := Nat.mul_le_mul_left _ h1
    _ ≤ Nat.card (stabilizer 0) := Level0.card_step

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
