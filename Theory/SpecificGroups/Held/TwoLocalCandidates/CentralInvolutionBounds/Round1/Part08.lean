module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Data

/-!
# Refinement 1, vertices 1024 through 1151

Kernel-checked equalities for the exact Held relation and involution.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem check1_8 : ∀ x : Fin 2058, 1024 ≤ x.val → x.val < 1152 →
    weight11 x.val = decode11 (signature weight10 x) := by
  apply Cores.allLetters
  decide +kernel
end Held.TwoLocalCandidates.CentralInvolutionBounds
