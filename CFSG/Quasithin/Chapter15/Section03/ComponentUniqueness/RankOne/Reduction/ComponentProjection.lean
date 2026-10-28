module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ComponentProjection.Algebra
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ComponentProjection.Normality

/-!
# Component containment from the inner action in 15.3.43

Construct `Y_L` as the two-residual of `L ∩ (Y₊ C_G(L))`. The actual
conjugation image and the central two-core of `L` give its nontriviality
and cubic two-core quotient. Its Sylow intersection lies in `S`, so the
residual-normalization argument places it in `M ∩ I`, and then in `Y₊`.
Normality and residual generation give equality. The noncentral subgroup
`Y₊` now fixes its component under `S`, and minimality gives `I = L S`.

The inner-action premise is explicit: the diagonal-exclusion producer and
the source reduction owner discharge it. All other inputs are the indicated
earlier local facts; neither containment nor relative normality is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, inner-action projection paragraph, printed p.1139.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
variable {G : Type*} [Group G] [Finite G]

/-- The containment and relative normality needed for the rank-one reduction.
`Y_L` is the defined subgroup, not an assumed projection witness. -/
theorem containment_and_relative_normality
    {Yplus S M I L : Subgroup G}
    (hI : I ∈ minimalOutsideFamily Yplus S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hLI : L ≤ I) (hL : Theory.GroupTheory.IsComponent I (L.subgroupOf I))
    (hLM : ¬ L ≤ M) (hSY : S ≤ normalizer (Yplus : Set G))
    (htheta : theta (M ⊓ I) = Yplus)
    (hN : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hres : Yplus = threeResidualIn (M ⊓ I))
    (hindex : (pCore 2 Yplus).index = 3)
    (hcenter : (center L).map L.subtype = L.pCoreIn 2)
    (hinner : ∀ y ∈ Yplus, ∃ l ∈ L, l⁻¹ * y ∈ centralizer (L : Set G)) :
    projection Yplus L = Yplus ∧ Yplus ≤ L ∧
      I = L ⊔ S ∧ I ≤ normalizer (L : Set G) ∧ (L.subgroupOf I).Normal := by
  have hpY : IsPPerfect 2 Yplus := htheta ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)
  have hZ : center L ≤ pCore 2 L := by
    intro z hz
    have hm := hcenter.le (mem_map_of_mem L.subtype hz)
    obtain ⟨w, hw, he⟩ := hm
    exact (L.subtype_injective he) ▸ hw
  obtain ⟨hne, hiA, hc⟩ := projection_algebra hinner hZ hpY hindex
    (component_action_ne_bot hLI hLM hN)
  obtain ⟨Q, hQ⟩ := projection_sylow_intersection P hP hLI hL hSY
  have hAM := le_intersection_of_projection_core
    ((projection_le_component Yplus L).trans hLI) hpY hSY hN Q hQ hc
  have hAY := le_residual_of_core_index hAM (projection_isPPerfect Yplus L) hiA hres
  have hYLnorm : Yplus ≤ normalizer (L : Set G) := by
    intro y hy
    obtain ⟨l, hl, hc⟩ := hinner y hy
    have hm := (normalizer (L : Set G)).mul_mem (L.le_normalizer hl)
      (Subgroup.centralizer_le_normalizer _ hc)
    simpa only [mul_inv_cancel_left] using hm
  have he := eq_of_normal_core_index hAY
    (normalizes_projection Yplus.le_normalizer hYLnorm)
    (projection_isPPerfect Yplus L) hne hpY hindex
  have hYL : Yplus ≤ L := he ▸ projection_le_component Yplus L
  exact ⟨he, hYL, relative_normality_of_containment hI P hP hLI hL hLM hYL hSY hN⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
