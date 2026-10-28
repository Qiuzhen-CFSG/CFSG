module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks00

/-! Kernel certificate for original normal-form indices 64 through 127.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_01 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 1 k) = orderFourTable (blockIndex 1 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
