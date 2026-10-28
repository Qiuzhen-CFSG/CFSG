module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks06

/-! Kernel certificate for original normal-form indices 448 through 511.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_07 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 7 k) = orderFourTable (blockIndex 7 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
