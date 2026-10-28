module
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Intersections controlled by a normal core

If a normal subgroup `R` and a subgroup `B` generate the ambient group,
and `[R,R]` lies in the normal core of `B`, then `R ∩ B` lies in that core.
The commutator bound makes `R` normalize the intersection, while normality
of `R` makes `B` normalize it. Their generating join therefore normalizes
the intersection, and maximality of the normal core gives the result.
No finiteness assumption is needed.

This general normal-core argument supports the residual/Frattini reduction
in Stellmacher (6.3), Journal of Algebra 190 (1997), p.31.
-/

namespace Subgroup

public theorem inf_le_normalCore_of_commutator_le
    {G : Type*} [Group G] (R B : Subgroup G) [R.Normal]
    (hgen : R ⊔ B = ⊤) (hcomm : ⁅R, R⁆ ≤ B.normalCore) :
    R ⊓ B ≤ B.normalCore := by
  have hR : R ≤ normalizer ((R ⊓ B : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact le_inf (commutator_le_right _ _)
      ((commutator_mono inf_le_left le_rfl).trans (hcomm.trans B.normalCore_le))
  have hB : B ≤ normalizer ((R ⊓ B : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    refine le_inf ((commutator_mono inf_le_left le_rfl).trans
      (commutator_le_left R B)) ?_
    exact (commutator_mono inf_le_right le_rfl).trans
      (by simpa using commutator_le_sup B B)
  let _ : (R ⊓ B).Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hR hB))
  exact normal_le_normalCore.mpr inf_le_right

end Subgroup
