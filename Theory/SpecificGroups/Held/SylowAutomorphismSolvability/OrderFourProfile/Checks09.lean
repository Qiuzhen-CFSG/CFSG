module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks08

/-! Kernel certificate for original normal-form indices 576 through 639.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_09 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 9 k) = orderFourTable (blockIndex 9 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
