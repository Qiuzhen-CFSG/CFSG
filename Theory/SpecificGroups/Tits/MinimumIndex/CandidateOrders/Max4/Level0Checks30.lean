module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Data

/-! Kernel checks for candidate max4, level 0, batches 30–39.
The witnesses and source conventions are documented in `Data.lean`. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max4
open Tits.Atlas1600OrderCertificate
set_option maxRecDepth 20000
set_option Elab.async false

public theorem L0batch30 : L0Batch 30 := by
  apply allFin₃
  decide +kernel

public theorem L0batch31 : L0Batch 31 := by
  apply allFin₃
  decide +kernel

public theorem L0batch32 : L0Batch 32 := by
  apply allFin₃
  decide +kernel

public theorem L0batch33 : L0Batch 33 := by
  apply allFin₃
  decide +kernel

public theorem L0batch34 : L0Batch 34 := by
  apply allFin₃
  decide +kernel

public theorem L0batch35 : L0Batch 35 := by
  apply allFin₃
  decide +kernel

public theorem L0batch36 : L0Batch 36 := by
  apply allFin₃
  decide +kernel

public theorem L0batch37 : L0Batch 37 := by
  apply allFin₃
  decide +kernel

public theorem L0batch38 : L0Batch 38 := by
  apply allFin₃
  decide +kernel

public theorem L0batch39 : L0Batch 39 := by
  apply allFin₃
  decide +kernel

end Tits.MinimumIndexCandidates.OrderCertificate.Max4
