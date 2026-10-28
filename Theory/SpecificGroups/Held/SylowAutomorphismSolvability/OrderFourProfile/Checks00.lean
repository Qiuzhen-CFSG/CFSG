module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.FiniteData

/-! Kernel certificate for original normal-form indices 0 through 63.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_00 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 0 k) = orderFourTable (blockIndex 0 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
