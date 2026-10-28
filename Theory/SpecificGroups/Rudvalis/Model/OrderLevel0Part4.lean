module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group3
import Mathlib.Tactic.FinCases

/-!
# Rudvalis forward transition certificates, part 5 of 7

The 29 batches in this part cover batch numbers congruent to 4 modulo 7.
For both forward generators, they establish the exact transitions on the
twenty fixed representatives in each batch. The first batch is algebraic;
the four imported groups cover the remaining batches 1–14, 15–20, 21–24,
and 25–28. All residual permutation identities are kernel-checked.

Witness source: the ATLAS degree-4060 generators and the word witnesses
documented in `OrderLevel0Data` and `OrderCertificate/GenerateChain.g`.
The statement agrees with `OrderCertificate/GenerateLevel0Part.py 4` and
supplies the part-4 input of `ForwardReduction.card_step_of_parts`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction
open Part4Certificates

public theorem part4 (b : Fin 29) : stepBatch ⟨7 * b.val + 4, by omega⟩ := by
  fin_cases b
  · exact firstBatch
  · exact group0 0
  · exact group0 1
  · exact group0 2
  · exact group0 3
  · exact group0 4
  · exact group0 5
  · exact group0 6
  · exact group0 7
  · exact group0 8
  · exact group0 9
  · exact group0 10
  · exact group0 11
  · exact group0 12
  · exact group0 13
  · exact group1 0
  · exact group1 1
  · exact group1 2
  · exact group1 3
  · exact group1 4
  · exact group1 5
  · exact group2 0
  · exact group2 1
  · exact group2 2
  · exact group2 3
  · exact group3 0
  · exact group3 1
  · exact group3 2
  · exact group3 3

end Rudvalis.OrderCertificate.ForwardReduction
