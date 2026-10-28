module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual3
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 4 of 7

Combine the word reductions and four pointwise residual certificates for the
29 batches congruent to 3 modulo 7. Source witnesses: `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction

public theorem part3 (b : Fin 29) : stepBatch ⟨7 * b.val + 3, by omega⟩ := by
  apply Part3Residual.part3_of_batches _ b
  intro g
  fin_cases g
  · exact Part3Residual.residuals0
  · exact Part3Residual.residuals1
  · exact Part3Residual.residuals2
  · exact Part3Residual.residuals3

end Rudvalis.OrderCertificate.ForwardReduction
