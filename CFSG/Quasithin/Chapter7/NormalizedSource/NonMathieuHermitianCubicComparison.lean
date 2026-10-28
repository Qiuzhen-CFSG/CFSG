module
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.SectionKernel
public import Theory.SpecificGroups.Janko4.PerfectCoverActions
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicOuterExclusion

/-!
# Full odd-actor comparison on the original J₄ cover

The actual component of the odd normalizer supplies a fixed involution in
C_V(T), its full M₂₂ centralizer residual, and a normal containing C-component
of C_G(z). The generic odd-actor comparison either places this component in
N_G(L) or produces the exceptional cubic action on its J₄ simple section.

In the latter case the existing cubic replacement, full-core transport and
native centralizer inversion exclude that action. These results require no
Mathieu marking on V. Thus the original residual lies in N_G(L) for every
odd elementary actor, including prime three, with all covering kernels kept.

The proof-only import deliberately reuses the internal generic comparison
chain from the Mathieu implementation. Its unrelated chapter exports remain
private, preserving the distinct existing rank-one and Mathieu interfaces.
Source: Aschbacher–Smith 4.4.3 and Remark 4.4.2, printed pp.619, 623,
as used in 7.4.1 on p.700, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The complete odd-actor comparison, retaining the original fixed involution,
full normal component and literal centralizer-residual inclusion. -/
theorem sourceOrbit_hermitian_janko_odd_fixed_residual_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    {p : ℕ} (hp : p.Prime) (hop : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ sectionCentralizer L) (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hn : K.Normal)
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hcent : centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)))
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
      ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G) := by
  let := hn
  let := hK.2
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  let := D.elementary
  let a := jankoNormalizerAction K e hcent
  have ho : Odd (Nat.card A) := by
    obtain ⟨n, hn⟩ := hAe.isPGroup.exists_card_eq
    rw [hn]
    exact hop.pow
  have hAk : (A.subgroupOf (normalizer (A : Set G))).map a.projection = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [a.kernel]
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv]
    exact ho.coprime_two_left
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    hV.symm ▸ D.sourceOrbit_weakClosure_setup.normalizes
  have hf := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) V T.isPGroup'
    (IsElementaryAbelian.isPGroup 2 V) hTV D.ne_bot
  obtain ⟨v, hv, hvne⟩ :=
    (V ⊓ centralizer ((T : Subgroup G) : Set G)).bot_or_exists_ne_one.resolve_left hf
  obtain ⟨k, hk, hkv⟩ := hVK hv.1
  let z : K := ⟨k, hk⟩
  have hzv : ((z : normalizer (A : Set G)) : G) = v := hkv
  have hz : orderOf z = 2 := by
    rw [← orderOf_coe z, ← orderOf_coe (z : normalizer (A : Set G)), hzv]
    exact orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian v hv.1, hvne⟩
  have hzV : ((z : normalizer (A : Set G)) : G) ∈ V := hzv.symm ▸ hv.1
  have hTz : (T : Subgroup G) ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) := by
    intro t ht
    rw [hzv]
    exact mem_centralizer_singleton_iff.mpr (hv.2 t ht)
  have hzG : orderOf (((z : normalizer (A : Set G)) : G)) = 2 := by
    rw [orderOf_coe, orderOf_coe]
    exact hz
  have hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hAV hx) _ hzV).symm
  obtain ⟨P, hP, hPn, ⟨eP⟩, hPm⟩ := janko_actor_residual_placement a hcent hAk z hz
  obtain ⟨Q, hQ, _⟩ := mathieu_residual_ambient_placement h.simpleQTKE hzG inf_le_left P hP eP
  let := hQ.2.2.1
  let := hQ.2.2.2
  rcases D.sourceOrbit_mathieu_oddActor_comparison_or_cubic_janko h
      hp hop A hne hAe hA _ hzG hTz hAz P hP eP Q hQ.2.1 with hQM | ⟨_, hmodel, x, hx, hcard⟩
  · refine ⟨z, hzV, hz, hTz, ?_⟩
    rw [←hPm]
    have hh := map_mono (f := (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype)
      hQ.2.1
    rw [map_map, subtype_comp_inclusion] at hh
    exact hh.trans hQM
  · exfalso
    have hcubic : MathieuJankoCubicSectionCase (T : Subgroup G) L V A :=
      ⟨K, hK, hn, hout, hVK, hFK, a, a.exists_mathieu_residual_seed,
        z, hzV, hz, hTz, P, hP, hPn, ⟨eP⟩, hPm, Q, hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2,
        hmodel, hAz, x, hx, hcard⟩
    have hseed := mathieu_janko_cubic_central_seed h hcubic
    have hrep := mathieu_janko_cubic_replacement h hseed
    have hcover := mathieu_janko_cubic_covered_replacement hrep
    have hfull := mathieu_janko_cubic_full_core h hcover
    exact mathieu_janko_cubic_first_row_impossible
      (mathieu_janko_cubic_first_row h hfull)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
