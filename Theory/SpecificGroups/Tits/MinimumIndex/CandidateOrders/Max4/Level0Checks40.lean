module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Data

/-! Kernel checks for candidate max4, level 0, batches 40–49.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max4
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L0batch40 : L0Batch 40 := by
  apply allFin₃
  decide +kernel

public theorem L0batch41 : L0Batch 41 := by
  apply allFin₃
  decide +kernel

public theorem L0batch42 : L0Batch 42 := by
  apply allFin₃
  decide +kernel

public theorem L0batch43 : L0Batch 43 := by
  apply allFin₃
  decide +kernel

public theorem L0batch44 : L0Batch 44 := by
  apply allFin₃
  decide +kernel

public theorem L0batch45 : L0Batch 45 := by
  apply allFin₃
  decide +kernel

public theorem L0batch46 : L0Batch 46 := by
  apply allFin₃
  decide +kernel

public theorem L0batch47 : L0Batch 47 := by
  apply allFin₃
  decide +kernel

public theorem L0batch48 : L0Batch 48 := by
  apply allFin₃
  decide +kernel

public theorem L0batch49 : L0Batch 49 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max4
