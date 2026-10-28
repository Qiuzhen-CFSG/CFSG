module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0Residual3
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 1 of 7

The 29 batches numbered 0 modulo 7 certify both forward generators on their
fixed representatives. The reduction proves 901 transitions algebraically;
the four residual certificates supply the remaining 259 permutation identities.
Together they prove all 1160 transitions without additional hypotheses.

Witness source: the ATLAS degree-4060 permutations and words in
`OrderLevel0Data`, documented in `OrderCertificate/GenerateChain.g`.
All residual identities are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction

/-- All forward transitions in the batches numbered 0 modulo 7. -/
public theorem part0 (b : Fin 29) : stepBatch ⟨7 * b.val + 0, by omega⟩ := by
  apply Part0Residual.part0_of_batches _ b
  intro g
  fin_cases g
  · exact Part0Residual.residuals0
  · exact Part0Residual.residuals1
  · exact Part0Residual.residuals2
  · exact Part0Residual.residuals3

end Rudvalis.OrderCertificate.ForwardReduction
