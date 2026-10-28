module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks03

/-! Kernel certificate for original normal-form indices 256 through 319.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_04 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 4 k) = orderFourTable (blockIndex 4 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
