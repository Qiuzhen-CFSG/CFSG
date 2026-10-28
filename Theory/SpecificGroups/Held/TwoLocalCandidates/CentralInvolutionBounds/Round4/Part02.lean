module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Data

/-!
# Refinement 4, vertices 256 through 383

Kernel-checked equalities for the exact Held relation and involution.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem check4_2 : ∀ x : Fin 2058, 256 ≤ x.val → x.val < 384 →
    weight41 x.val = decode41 (signature weight40 x) := by
  apply Cores.allLetters
  decide +kernel
end Held.TwoLocalCandidates.CentralInvolutionBounds
