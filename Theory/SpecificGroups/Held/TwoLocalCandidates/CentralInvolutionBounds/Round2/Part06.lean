module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Data

/-!
# Refinement 2, vertices 768 through 895

Kernel-checked equalities for the exact Held relation and involution.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem check2_6 : ∀ x : Fin 2058, 768 ≤ x.val → x.val < 896 →
    weight21 x.val = decode21 (signature weight20 x) := by
  apply Cores.allLetters
  decide +kernel
end Held.TwoLocalCandidates.CentralInvolutionBounds
