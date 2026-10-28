module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Batch15
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Batch16
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Batch17
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Batch18
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Batch19
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Batch20
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-4 batches 15–20

Combine the six independently checked batches. Residual permutation identities
use compressed factors whose expansions and lookup tables are kernel-checked.
Source: the ATLAS witnesses documented in `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates

public theorem group1 (b : Fin 6) :
    stepBatch ⟨7 * (b.val + 15) + 4, by omega⟩ := by
  fin_cases b
  · exact group1Batch15
  · exact group1Batch16
  · exact group1Batch17
  · exact group1Batch18
  · exact group1Batch19
  · exact group1Batch20

end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
