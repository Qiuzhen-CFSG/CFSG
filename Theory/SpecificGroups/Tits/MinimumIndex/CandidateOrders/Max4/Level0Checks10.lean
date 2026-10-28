module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Data

/-! Kernel checks for candidate max4, level 0, batches 10–19.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max4
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L0batch10 : L0Batch 10 := by
  apply allFin₃
  decide +kernel

public theorem L0batch11 : L0Batch 11 := by
  apply allFin₃
  decide +kernel

public theorem L0batch12 : L0Batch 12 := by
  apply allFin₃
  decide +kernel

public theorem L0batch13 : L0Batch 13 := by
  apply allFin₃
  decide +kernel

public theorem L0batch14 : L0Batch 14 := by
  apply allFin₃
  decide +kernel

public theorem L0batch15 : L0Batch 15 := by
  apply allFin₃
  decide +kernel

public theorem L0batch16 : L0Batch 16 := by
  apply allFin₃
  decide +kernel

public theorem L0batch17 : L0Batch 17 := by
  apply allFin₃
  decide +kernel

public theorem L0batch18 : L0Batch 18 := by
  apply allFin₃
  decide +kernel

public theorem L0batch19 : L0Batch 19 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max4
