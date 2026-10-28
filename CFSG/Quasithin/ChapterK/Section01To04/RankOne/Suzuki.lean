module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Suzuki.Ratios

/-!
# The Suzuki natural-module branch of K.3.6

For the genuine natural-module identification, the original actor has odd
quotient by its Suzuki layer, which is its prime-to-two residual. Its Sylow
omega has rank r, is quadratic, and fixes exactly 2r of the 4r binary
dimensions. Every involution is free: the displacement image equals its
kernel. All nontrivial elementary actors have fixed codimension 2r and rank
at most r. Hence both action ratios are two, and Ω₁(T) is the unique member
of the source threshold family Q(T,V).

The module identification is the independently proved recognition input;
none of these conclusions is assumed. All subgroups and actions below remain
in the original G and V. Source: Aschbacher–Smith, K.3.6, printed p.457,
and Definition D.2.1, printed p.178 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne
open Subgroup Representation.BinaryOffender
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {m : ℕ} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- K.3.6 on the original source domain, after genuine natural-module recognition. -/
theorem SourceHypotheses.suzuki_case (h : SourceHypotheses ρ L)
    (M : SuzukiModel m ρ L) (hm : 1 ≤ m) (T : Sylow 2 G) :
    Odd L.index ∧ primeToResidual 2 G = L ∧ (T : Subgroup G) ≤ L ∧
    IsElementaryTwo (omegaOneAmbient (T : Subgroup G)) ∧
    rank (omegaOneAmbient (T : Subgroup G)) = 2 * m + 1 ∧
    Module.finrank (ZMod 2) V = 4 * (2 * m + 1) ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient (T : Subgroup G))) =
      2 * (2 * m + 1) ∧
    (∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      LinearMap.range (ρ t - LinearMap.id) = LinearMap.ker (ρ t - LinearMap.id)) ∧
    IsQuadratic ρ (omegaOneAmbient (T : Subgroup G)) ∧
    actionRatio ρ (omegaOneAmbient (T : Subgroup G)) = 2 ∧
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 ∧
    {A : Subgroup G | A ≤ T ∧ IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2} =
      {omegaOneAmbient (T : Subgroup G)} := by
  have ho := h.suzuki_omega_calculation M hm T
  have hr := h.suzuki_ratios M hm
  exact ⟨h.suzuki_odd_index M hm, h.suzuki_primeToResidual M hm,
    h.suzuki_sylow_le M hm T, ho.1, ho.2, M.finrank_eq,
    h.suzuki_omega_fixed_finrank M hm T, h.suzuki_involution_free M hm,
    h.suzuki_omega_quadratic M hm T, h.suzuki_omega_ratio M hm T,
    hr.1, hr.2, h.suzuki_threshold_family M hm T⟩

end CFSG.Quasithin.ChapterK.RankOne
