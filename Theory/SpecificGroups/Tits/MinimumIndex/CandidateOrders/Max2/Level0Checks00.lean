module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Data

/-! Kernel checks for candidate max2, level 0, batches 0–9.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max2
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L0batch0 : L0Batch 0 := by
  apply allFin₃
  decide +kernel

public theorem L0batch1 : L0Batch 1 := by
  apply allFin₃
  decide +kernel

public theorem L0batch2 : L0Batch 2 := by
  apply allFin₃
  decide +kernel

public theorem L0batch3 : L0Batch 3 := by
  apply allFin₃
  decide +kernel

public theorem L0batch4 : L0Batch 4 := by
  apply allFin₃
  decide +kernel

public theorem L0batch5 : L0Batch 5 := by
  apply allFin₃
  decide +kernel

public theorem L0batch6 : L0Batch 6 := by
  apply allFin₃
  decide +kernel

public theorem L0batch7 : L0Batch 7 := by
  apply allFin₃
  decide +kernel

public theorem L0batch8 : L0Batch 8 := by
  apply allFin₃
  decide +kernel

public theorem L0batch9 : L0Batch 9 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max2
