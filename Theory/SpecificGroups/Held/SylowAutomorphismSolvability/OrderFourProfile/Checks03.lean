module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks02

/-! Kernel certificate for original normal-form indices 192 through 255.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_03 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 3 k) = orderFourTable (blockIndex 3 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
