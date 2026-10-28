module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Data

/-!
# Refinement 1, vertices 1536 through 1663

Kernel-checked equalities for the exact Held relation and involution.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem check1_12 : ∀ x : Fin 2058, 1536 ≤ x.val → x.val < 1664 →
    weight11 x.val = decode11 (signature weight10 x) := by
  apply Cores.allLetters
  decide +kernel
end Held.TwoLocalCandidates.CentralInvolutionBounds
