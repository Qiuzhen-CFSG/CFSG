module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Data

/-! Kernel checks for candidate max2, level 0, batches 10–10.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max2
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L0batch10 : L0Batch 10 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max2
