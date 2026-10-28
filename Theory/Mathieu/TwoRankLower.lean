module

public import Theory.Mathieu.M12.SmallParabolicPair.Geometry
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Mathieu.M22.Properties.LocalSubgroups
public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow.Checks
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.Candidates
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Elementary-subgroup lower bounds for the Mathieu two-ranks

The actual marked elementary subgroups have orders 8, 16, 16 and 64 in
M₁₂, M₂₂, M₂₃ and M₂₄. Their inclusions supply the respective rank lower
bounds, without an assumed rank table or order-based inference of rank.
Source application: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
namespace Sporadic.Mathieu

/-- The marked elementary eight witnesses the lower bound for M₁₂. -/
theorem m12_three_le_twoRank : 3 ≤ primeRank 2 M12 :=
  IsElementaryAbelian.primeRank_ge_of_card M12SmallPair.elementary
    M12SmallPair.card_elementary

/-- A pointwise hexad kernel witnesses rank four in M₂₂. -/
theorem m22_four_le_twoRank : 4 ≤ primeRank 2 M22 := by
  let : IsElementaryAbelian 2 (m22HexadPointwiseKernel m22Hexad123) :=
    m22HexadPointwiseKernel_elementaryAbelian m22Hexad123_mem
  exact IsElementaryAbelian.primeRank_ge_of_card _
    (m22HexadPointwiseKernel_card m22Hexad123_mem)

/-- The explicit elementary Sylow candidate witnesses rank four in M₂₃. -/
theorem m23_four_le_twoRank : 4 ≤ primeRank 2 M23 := by
  let : IsElementaryAbelian 2 (M23Geometry.ElementarySylow.candidate 0) :=
    M23Geometry.ElementarySylow.candidate_elementary 0
  exact IsElementaryAbelian.primeRank_ge_of_card _
    (M23Geometry.ElementarySylow.candidate_card 0)

/-- The sextet elementary subgroup witnesses rank six in M₂₄. -/
theorem m24_six_le_twoRank : 6 ≤ primeRank 2 M24 :=
  IsElementaryAbelian.primeRank_ge_of_card (M24LocalGeometry.EvenCandidates.elementary 0)
    (M24ChapterHStabilizers.ElementaryFusion.candidate_card 0)

end Sporadic.Mathieu
