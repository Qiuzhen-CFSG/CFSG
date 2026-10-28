module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.Action

/-!
# Zero-image commutation tests, points 768–1023

This block kernel-checks the four tests against the actual representative
words. Splitting the exhaustive calculation bounds compilation cost; the
range bounds are discharged in `Constraints`.
Source: ATLAS HeG1-p2058B0 and the words in Calculations/Source.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem zero_candidates_3 : ∀ x : Fin 2058,
    768 ≤ x.val → x.val < 1024 → test0 x → x = 0 ∨ x = 1395 := by
  decide +kernel

end Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer
