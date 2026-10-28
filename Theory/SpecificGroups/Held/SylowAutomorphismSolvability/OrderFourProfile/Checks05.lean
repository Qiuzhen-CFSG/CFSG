module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks04

/-! Kernel certificate for original normal-form indices 320 through 383.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_05 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 5 k) = orderFourTable (blockIndex 5 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
