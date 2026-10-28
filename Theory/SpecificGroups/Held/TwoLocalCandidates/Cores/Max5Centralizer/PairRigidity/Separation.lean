module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.ThreeData

/-!
# Terminal separation and unequal color counts

Kernel evaluation checks a count discrepancy in the two second-round
tables and recovers all vertices from the third-round table. The final
proof also uses every preceding decoding certificate; these data alone
are not a rigidity or nonisomorphism assumption.
Source: GLS3 Table 5.3p, the Held 2B extraspecial centralizer.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.Certificate

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem left_count : colorCount left2 4906631 = 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem right_count : colorCount right2 4906631 = 1 := by
  decide +kernel

public theorem counts_ne : colorCount left2 4906631 ≠ colorCount right2 4906631 := by
  rw [left_count, right_count]
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem separating : ∀ x : Fin 2058,
    decodeVertex (left3 x.val) = x.val := by
  apply allLetters
  decide +kernel

end Held.TwoLocalCandidates.Cores.Max5Centralizer.PairRigidity.Certificate
