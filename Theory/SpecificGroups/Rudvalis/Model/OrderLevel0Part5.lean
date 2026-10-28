module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Residual3
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 6 of 7

The 29 batches cover batch numbers congruent to 5 modulo 7, certifying both
forward generators on 580 representatives. The first six batches and the
algebraic word reductions are supplied by `OrderLevel0Part5ResidualReduction`;
the four residual certificates discharge all 275 remaining permutation checks.

Source: the fixed ATLAS degree-4060 witnesses in `OrderLevel0Data`, documented
in `OrderCertificate/GenerateChain.g`. Every transition is kernel-checked.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction

/-- Both forward generators satisfy the fixed transition identities in part 5. -/
public theorem part5 (b : Fin 29) : stepBatch ⟨7 * b.val + 5, by omega⟩ := by
  apply Part5Residual.part5_of_batches _ b
  intro g
  fin_cases g
  · exact Part5Residual.residuals0
  · exact Part5Residual.residuals1
  · exact Part5Residual.residuals2
  · exact Part5Residual.residuals3

end Rudvalis.OrderCertificate.ForwardReduction
