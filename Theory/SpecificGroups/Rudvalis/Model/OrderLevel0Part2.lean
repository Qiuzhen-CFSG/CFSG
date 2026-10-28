module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual3
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 3 of 7

Assemble the algebraic transitions and the four residual certificates for
batch numbers congruent to 2 modulo 7. Witness source: `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction

public theorem part2 (b : Fin 29) : stepBatch ⟨7 * b.val + 2, by omega⟩ := by
  apply Part2Residual.part2_of_batches _ b
  intro g
  fin_cases g
  · exact Part2Residual.residuals0
  · exact Part2Residual.residuals1
  · exact Part2Residual.residuals2
  · exact Part2Residual.residuals3

end Rudvalis.OrderCertificate.ForwardReduction
