module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks10

/-! Kernel certificate for original normal-form indices 704 through 767.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_11 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 11 k) = orderFourTable (blockIndex 11 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
