module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.NoncentralSporadic.Basic

/-!
# Reduction to intrinsic fusion of the common residual

For u = cv, elementary T_C gives c² = v² = 1. Since c centralizes L, v
centralizes the actual X = O²(C_L(u)). The earlier two-central exclusion
makes v lie outside X once all involutions of X are two-central. The existing
coset-fusion theorem then constructs its nonidentity conjugate product.

This is a conditional reduction, not the completed sporadic exclusion. The
covering and model proofs must supply centerlessness and the three intrinsic
residual/fusion assertions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.5.11, printed p.1200, together with 16.4.9(3) and 16.5.10(5).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.NoncentralSporadic

open Subgroup
open scoped IsMulCommutative

/-- A centerless subgroup intersects its ambient centralizer trivially. -/
theorem disjoint_centralizer_of_center_eq_bot {G : Type*} [Group G]
    {L : Subgroup G} (hZ : center L = ⊥) :
    Disjoint L (centralizer (L : Set G)) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hc
  have hz : (⟨x, hx⟩ : L) ∈ center L :=
    mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hc y y.property)
  rw [hZ, mem_bot] at hz
  exact congrArg Subtype.val hz

/-- Cancelling the commuting factor shows that v centralizes the actual X. -/
theorem projection_centralizes_commonResidual {G : Type*} [Group G]
    {L : Subgroup G} {u c v : G}
    (hc : c ∈ centralizer (L : Set G)) (he : u = c * v) :
    v ∈ centralizer (commonResidual L u : Set G) := by
  apply mem_centralizer_iff.mpr
  intro x hx
  have hx' := commonResidual_le L u hx
  have hxc := mem_centralizer_iff.mp hc x hx'.1
  have hxu := mem_centralizer_singleton_iff.mp hx'.2
  apply mul_left_cancel (a := c)
  calc
    c * (x * v) = x * (c * v) := by rw [← mul_assoc, ← hxc, mul_assoc]
    _ = (c * v) * x := by rwa [← he]
    _ = c * (v * x) := mul_assoc _ _ _

/-- Discharge the structural inputs to the existing coset-product obstruction.
The remaining intrinsic obligations are an involution in the actual residual,
its two-centrality, and the fusion of its involution coset. The hypotheses
`hdetect` and `havoid` are the earlier 16.4.9(3) and centerless 16.5.10(5) inputs.
No conjugate-product witness is assumed. -/
theorem false_of_common_residual_fusion {G : Type*} [Group G]
    {L C : Subgroup G} [IsElementaryAbelian 2 C] {g u c v : G}
    (hZ : center L = ⊥) (hC : C ≤ centralizer (L : Set G))
    (hdelta : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (hgX : g ∈ normalizer (commonResidual L u : Set G))
    (hu : u ∈ (centralizer (L : Set G)).conjBy g) (hu2 : orderOf u = 2)
    (huK : u ∉ centralizer (L : Set G))
    (hc : c ∈ C) (hv : v ∈ L) (he : u = c * v)
    (hinvolution : ∃ x ∈ commonResidual L u, orderOf x = 2)
    (hfuse : InvolutionCosetFusion L (commonResidual L u) v)
    (htwoCentral : ∀ x ∈ commonResidual L u, orderOf x = 2 → IsTwoCentralIn L x)
    (hdetect : ∀ (J : Subgroup G),
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
        i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
        J ∈ deltaZero L)
    (havoid : ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsTwoCentralIn L w) : False := by
  have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hc
  have hv2 : orderOf v = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨projection_square_eq_one hC hc hv
      (by rw [← hu2, pow_orderOf_eq_one]) he, ?_⟩
    intro hv1
    exact huK (by simpa [he, hv1] using hC hc)
  have hvX : v ∉ commonResidual L u := by
    intro hvX
    exact havoid _ hdelta u c v hu hu2 (hC hc) hv he (htwoCentral v hvX hv2)
  exact coset_fusion_obstruction (disjoint_centralizer_of_center_eq_bot hZ)
    ((commonResidual_le L u).trans inf_le_left) hgX hu hu2 (hC hc)
    (by simpa only [pow_two] using hc2) hv hv2 he hvX
    (projection_centralizes_commonResidual (hC hc) he) hinvolution hfuse htwoCentral
    hdetect havoid

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.NoncentralSporadic
