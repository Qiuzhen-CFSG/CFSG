module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 index certificate

The three forward generators suffice for the 1024-coset transversal.
Their inverse transitions and the index formula are proved in
`OrderLevel2Reduction`; the three `OrderLevel2Positive` modules certify all
forward transitions in kernel-checked batches. This establishes the index
without further hypotheses. The forward witnesses come from the ATLAS degree-4060
data documented in `OrderLevel2Data` and `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate
open Theory.GroupTheory

/-- Assemble the three forward transition certificates. -/
public theorem H2_card_step_of_positive
    (h0 : ∀ r : Fin 1024,
      L2Gen 0 * L2Rep r = L2Rep (L2Act 0 r) * evalWord L3Gen (L2Factor 0 r))
    (h1 : ∀ r : Fin 1024,
      L2Gen 1 * L2Rep r = L2Rep (L2Act 1 r) * evalWord L3Gen (L2Factor 1 r))
    (h2 : ∀ r : Fin 1024,
      L2Gen 2 * L2Rep r = L2Rep (L2Act 2 r) * evalWord L3Gen (L2Factor 2 r)) :
    Nat.card H2 = 1024 * Nat.card H3 := by
  apply Level2Reduction.card_step_of_positive
  intro i r
  fin_cases i
  · exact h0 r
  · exact h1 r
  · exact h2 r

/-- The level-2 subgroup has 1024 cosets of the level-3 subgroup. -/
public theorem H2_card_step : Nat.card H2 = 1024 * Nat.card H3 := by
  exact H2_card_step_of_positive
    OrderLevel2Positive0.positiveStep
    OrderLevel2Positive1.positiveStep
    OrderLevel2Positive2.positiveStep

end Rudvalis.OrderCertificate
