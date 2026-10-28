module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 7 of 7

The 29 batches numbered 6 modulo 7 certify both forward generators on their
fixed representatives. Assemble the first three algebraic batches and the
three independently checked blocks covering the remaining 26 batches.
Together they prove all 1160 transitions without additional hypotheses.

Witness source: the ATLAS degree-4060 permutations and words in
`OrderLevel0Data`, documented in `OrderCertificate/GenerateChain.g`.
All residual identities are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction

/-- All forward transitions in the batches numbered 6 modulo 7. -/
public theorem part6 (b : Fin 29) : stepBatch ⟨7 * b.val + 6, by omega⟩ := by
  fin_cases b
  · exact Part6Base.first 0
  · exact Part6Base.first 1
  · exact Part6Base.first 2
  · exact Part6Block0.checked 0
  · exact Part6Block0.checked 1
  · exact Part6Block0.checked 2
  · exact Part6Block0.checked 3
  · exact Part6Block0.checked 4
  · exact Part6Block0.checked 5
  · exact Part6Block0.checked 6
  · exact Part6Block0.checked 7
  · exact Part6Block0.checked 8
  · exact Part6Block0.checked 9
  · exact Part6Block0.checked 10
  · exact Part6Block0.checked 11
  · exact Part6Block0.checked 12
  · exact Part6Block0.checked 13
  · exact Part6Block1.checked 0
  · exact Part6Block1.checked 1
  · exact Part6Block1.checked 2
  · exact Part6Block1.checked 3
  · exact Part6Block1.checked 4
  · exact Part6Block1.checked 5
  · exact Part6Block1.checked 6
  · exact Part6Block2.checked 0
  · exact Part6Block2.checked 1
  · exact Part6Block2.checked 2
  · exact Part6Block2.checked 3
  · exact Part6Block2.checked 4

end Rudvalis.OrderCertificate.ForwardReduction
