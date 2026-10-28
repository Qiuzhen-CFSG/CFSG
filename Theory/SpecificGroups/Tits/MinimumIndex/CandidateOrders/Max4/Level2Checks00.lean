module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Data

/-! Kernel checks for candidate max4, level 2, batches 0–0.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max4
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L2batch0 : L2Batch 0 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max4
