module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks12

/-! Kernel certificate for original normal-form indices 832 through 895.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_13 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 13 k) = orderFourTable (blockIndex 13 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
