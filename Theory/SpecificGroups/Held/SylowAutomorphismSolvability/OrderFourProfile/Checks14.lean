module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks13

/-! Kernel certificate for original normal-form indices 896 through 959.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_14 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 14 k) = orderFourTable (blockIndex 14 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
