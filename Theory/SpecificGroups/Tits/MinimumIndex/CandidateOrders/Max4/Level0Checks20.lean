module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Data

/-! Kernel checks for candidate max4, level 0, batches 20–29.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max4
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L0batch20 : L0Batch 20 := by
  apply allFin₃
  decide +kernel

public theorem L0batch21 : L0Batch 21 := by
  apply allFin₃
  decide +kernel

public theorem L0batch22 : L0Batch 22 := by
  apply allFin₃
  decide +kernel

public theorem L0batch23 : L0Batch 23 := by
  apply allFin₃
  decide +kernel

public theorem L0batch24 : L0Batch 24 := by
  apply allFin₃
  decide +kernel

public theorem L0batch25 : L0Batch 25 := by
  apply allFin₃
  decide +kernel

public theorem L0batch26 : L0Batch 26 := by
  apply allFin₃
  decide +kernel

public theorem L0batch27 : L0Batch 27 := by
  apply allFin₃
  decide +kernel

public theorem L0batch28 : L0Batch 28 := by
  apply allFin₃
  decide +kernel

public theorem L0batch29 : L0Batch 29 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max4
