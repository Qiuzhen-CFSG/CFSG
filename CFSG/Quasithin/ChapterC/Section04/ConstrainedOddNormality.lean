module
public import Theory.GroupTheory.CComponent.OddRankNormal
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedCubicNormality
public import Theory.SpecificGroups.Classical.PairedOddRank

/-!
# Odd-rank normality for the selected constrained component

The source bounds the core center by one or three. Cubic rank is handled
by the intersection argument; at every other odd prime the center is
coprime, so distinct conjugates would violate the ambient rank bound.
The actual star central-cover map transports the rank witness.

For SL₃ over a binary field of degree greater than one, the proved torus
and cycle witnesses supply such an odd prime in every field degree. Thus
the literal selected component is normal, without any normalizer-geometry
or desired original-component normality premise.

Source: Aschbacher–Smith C.2.7(1), C.4.5, printed pp.145,152.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
theorem constrained_component_normal_of_central_oddRank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 2 ≤ primeRank p (coreCentralQuotient K)) : K.Normal := by
  by_cases h3 : p = 3
  · subst p
    exact h.constrained_component_normal_of_central_threeRank K hK hq hout hfK hr
  let := hq
  let : Fact p.Prime := ⟨hp⟩
  have hc : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) := by
    let eK := K.equivMapOfInjective H.subtype H.subtype_injective
    let e := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
    have hc := C27Source.coreQuotient_center_card_from_source
      (h.constrained_source_input K hK hq hout hfK)
    rw [Nat.card_congr (centerCongr e).toEquiv]
    rcases hc with hc | hc
    · rw [hc]
      exact Nat.coprime_one_right p
    · rw [hc]
      exact hp.coprime_iff_not_dvd.mpr (fun hd => h3
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  have hrK : 2 ≤ primeRank p (K ⧸ pCore 2 K) := by
    by_contra! hlt
    let P : Sylow p (K ⧸ pCore 2 K) := Classical.choice inferInstance
    have hh := P.primeRank_quotient_le_one
      (P.isCyclic_of_odd_of_primeRank_le_one ho (by omega)) (center (K ⧸ pCore 2 K))
    change primeRank p (coreCentralQuotient K) ≤ 1 at hh
    omega
  exact hK.normal_of_coprime_core_center_primeRank ho hc hrK (h.sqtk.stronglyQuasithin p hp ho)

theorem constrained_linear_three_component_normal
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : K.Normal := by
  let ec := (h.constrained_star_central_equiv K hK hq hout hfK).trans
    (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e))
  obtain ⟨p,hp,ho,hr⟩ := Theory.SpecificGroups.Classical.PairedOddRank.linear_binary_exists hF F.card_eq
  apply h.constrained_component_normal_of_central_oddRank K hK hq hout hfK hp ho
  rwa [primeRank_congr p ec]
end CFSG.Quasithin.ChapterC.HypothesisC28
