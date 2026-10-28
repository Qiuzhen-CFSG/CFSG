module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Data
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-1 index certificate

The 1755 representatives form a transversal for the fixed subgroup `H2` in `H1`.
The two positive-generator transition certificates are proved in kernel-checked
batches. `OrderLevel1Reduction` derives the inverse transitions using reversed
inverse factor words, then applies the word-subgroup cardinality theorem at
base point 1. All transition premises are discharged here.

Source: the ATLAS degree-4060 witnesses documented in `OrderLevel1Data`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate

/-- The level-1 subgroup has 1755 cosets of the level-2 subgroup. -/
public theorem H1_card_step : Nat.card H1 = 1755 * Nat.card H2 := by
  apply Level1Reduction.card_step_of_positive
  intro i r
  fin_cases i
  · exact L1PositiveStep0 r
  · exact L1PositiveStep1 r

end Rudvalis.OrderCertificate
