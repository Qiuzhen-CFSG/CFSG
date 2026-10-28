module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Data

/-! Kernel checks for candidate max4, level 0, batches 50–59.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max4
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L0batch50 : L0Batch 50 := by
  apply allFin₃
  decide +kernel

public theorem L0batch51 : L0Batch 51 := by
  apply allFin₃
  decide +kernel

public theorem L0batch52 : L0Batch 52 := by
  apply allFin₃
  decide +kernel

public theorem L0batch53 : L0Batch 53 := by
  apply allFin₃
  decide +kernel

public theorem L0batch54 : L0Batch 54 := by
  apply allFin₃
  decide +kernel

public theorem L0batch55 : L0Batch 55 := by
  apply allFin₃
  decide +kernel

public theorem L0batch56 : L0Batch 56 := by
  apply allFin₃
  decide +kernel

public theorem L0batch57 : L0Batch 57 := by
  apply allFin₃
  decide +kernel

public theorem L0batch58 : L0Batch 58 := by
  apply allFin₃
  decide +kernel

public theorem L0batch59 : L0Batch 59 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max4
