module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks09

/-! Kernel certificate for original normal-form indices 640 through 703.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_10 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 10 k) = orderFourTable (blockIndex 10 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
