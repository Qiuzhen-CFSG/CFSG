module
public import Theory.SpecificGroups.Suzuki.BorelResidualRigidity
public import Theory.GroupTheory.PResidual.PerfectCentralLift

/-!
# Two-perfect Borels in perfect Suzuki central covers

The lifted Sylow normalizer maps onto the Borel in the actual Suzuki
quotient, which is two-perfect. Its index is odd and its kernel is a central
two-group. Transfer in the perfect covering group removes the central
supplement to the lifted residual, proving the entire Borel two-perfect.

This is the B₀ = O²(B₀) assertion in Aschbacher--Smith 15.1.21(i),
printed pp.1097--1098. No splitting or multiplier order is required.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups
variable {H : Type*} [Group H] [Finite H] [Group.IsPerfect H] {m : ℕ}

/-- The full Borel in a perfect central two-cover is two-perfect. -/
theorem suzuki_coverBorel_isPPerfect
    (hc : pCore 2 H ≤ center H) (hm : 0 < m)
    (e : (H ⧸ pCore 2 H) ≃* SuzukiMatrixGroup m) (P : Sylow 2 H) :
    IsPPerfect 2 (normalizer (P : Set H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hkq : q.ker = pCore 2 H := QuotientGroup.ker_mk' _
  apply isPPerfect_of_central_pKernel_image q (normalizer (P : Set H))
    (hkq.le.trans hc)
    (by rw [hkq]; exact pCore_isPGroup)
  · rw [hkq]
    exact (pCore_isPGroup.le_sylow_of_normal P).trans (P : Subgroup H).le_normalizer
  · intro hd
    exact P.not_dvd_index (hd.trans (index_dvd_of_le (P : Subgroup H).le_normalizer))
  · rw [P.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)]
    exact (pResidual_eq_top_iff 2 _).mp
      (suzuki_sylowNormalizer_pResidual_eq_top hm e
        (P.mapSurjective (QuotientGroup.mk'_surjective _)))

end BenderSuzuki.MatrixGroups
