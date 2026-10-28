module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks14

/-! Kernel certificate for original normal-form indices 960 through 1023.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_15 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 15 k) = orderFourTable (blockIndex 15 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
