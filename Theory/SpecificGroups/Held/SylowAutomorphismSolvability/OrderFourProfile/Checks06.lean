module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks05

/-! Kernel certificate for original normal-form indices 384 through 447.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_06 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 6 k) = orderFourTable (blockIndex 6 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
