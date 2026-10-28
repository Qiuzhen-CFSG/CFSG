module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks11

/-! Kernel certificate for original normal-form indices 768 through 831.
The dependency chain bounds certificate memory during parallel Lake builds.
Source: the actual ATLAS action and the proposed flags in `FiniteData`. -/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile

public theorem orderFour_block_12 : ∀ k : Fin 64,
    hasOrderFour (blockIndex 12 k) = orderFourTable (blockIndex 12 k) := by
  decide +kernel

end Held.SylowAutomorphismSolvability.OrderFourProfile
