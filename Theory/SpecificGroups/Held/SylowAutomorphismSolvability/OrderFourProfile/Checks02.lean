module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks01

/-! Kernel certificate for original normal-form indices 128 through 191.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_02 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 2 k) = orderFourTable (blockIndex 2 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
