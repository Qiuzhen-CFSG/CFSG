module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks07

/-! Kernel certificate for original normal-form indices 512 through 575.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_08 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 8 k) = orderFourTable (blockIndex 8 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
