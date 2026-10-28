module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8.Data

/-! Kernel checks for candidate max8, level 1, batches 0–0.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max8
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L1batch0 : L1Batch 0 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max8
