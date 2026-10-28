module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Batch24
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Batch25
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Batch26
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Batch27
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Batch28
import Mathlib.Tactic.FinCases
/-!
# Rudvalis part-6 batches 24–28

Combine the five batch certificates. Their kernel-checked composition tables
use the ATLAS witnesses in `OrderLevel0Data` and `OrderChainData`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block2
public theorem checked (b : Fin 5) :
    stepBatch ⟨7 * (b.val + 24) + 6, by omega⟩ := by
  fin_cases b
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
end Rudvalis.OrderCertificate.ForwardReduction.Part6Block2
