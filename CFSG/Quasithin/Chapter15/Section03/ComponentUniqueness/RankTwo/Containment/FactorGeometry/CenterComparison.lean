module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.TwoComponents
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.InitialModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.RankOneModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankZero

/-!
# The center and rank comparison at the start of 15.3.39

Strict containment in the S-orbit makes the ordinary component nonnormal
in I. If it had three-rank at least two, it would contain an elementary
abelian group of order nine. A distinct conjugate commutes with it and
contains an element of order three. That element cannot lie in the first
component: its center is a two-group because its odd core is trivial.
Their join therefore has rank at least three, contradicting the local SQTK
bound. The positive-rank conclusion of 15.3.34 gives three-rank exactly one.

The normalizer-index and complete quotient-model alternative of 1.2.1(3)
are also extracted, using the actual Sylow realization and actual quotient
equivalence. The rank argument does not require a model-list inspection.

The complete rank-one reduction of all six alternatives of 1.1.5(3)
gives trivial two-core. Since the center lies in that core, it is trivial.
`centerless_comparison_of_source_inputs` supplies the exact function expected
by `OrbitEquality`, with no remaining model-reduction premise. Its earlier
inputs are the genuine 15.3.33(3) conclusions, the local SQTK rank bound,
and the positive-rank clause of 15.3.34. The nonnormal model alternative
of 1.2.1(3) is preserved separately and supplies the orbit-index bound
in the consumer `CenterComparison.OrbitEquality`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3)
and 1.2.1(3), printed pp.501--504; 15.3.33(3), 15.3.34 and 15.3.39,
printed pp.1134 and 1137--1138.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem center_le_twoCore_of_oddCore_eq_bot
    {K : Type*} [Group K] [Finite K] (hodd : pPrimeCore 2 K = ⊥) :
    center K ≤ pCore 2 K := by
  have hc : center K ≤ fittingSubgroup K := le_sSup ⟨inferInstance, inferInstance⟩
  exact hc.trans (Fitting_eq_pcore K 2 hodd).le

private theorem exists_elementaryNine_of_rank (h : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  classical
  let P : Sylow 3 G := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hr := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨E, _, hcard, he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let := he
  refine ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective] using hcard

private theorem normal_of_two_le_three_rank {K : Subgroup G}
    (hK : IsComponent G K) (hodd : pPrimeCore 2 K = ⊥)
    (hrankK : 2 ≤ primeRank 3 K) (hrankG : primeRank 3 G ≤ 2) : K.Normal := by
  classical
  have hcore := center_le_twoCore_of_oddCore_eq_bot hodd
  obtain ⟨A, hA, hAc⟩ := exists_elementaryNine_of_rank hrankK
  let := hA
  let E := A.map K.subtype
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map_subtype
  have hEc : Nat.card E = 3 ^ 2 := by
    simpa only [E, Subgroup.card_map_of_injective K.subtype_injective] using hAc
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  have hc : K.map (MulAut.conj g).toMonoidHom ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      ((hK.map_conj g).commutator_eq_bot_of_ne hK hne)
  have hd : 3 ∣ Nat.card K := by
    by_contra hn
    have hz : primeRank 3 K = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hd
  let e := (MulAut.conj g).subgroupMap K
  let x := e a
  have hxG : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe, show orderOf x = orderOf a from e.orderOf_eq a, ha]
  have hxC : (x : G) ∈ centralizer (K : Set G) := hc x.property
  have hxK : (x : G) ∉ K := by
    intro hxK
    have hz : (⟨x, hxK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (mem_centralizer_iff.mp hxC k k.property)
    have hp := (pCore_isPGroup (p := 2) (G := K)).orderOf_coprime
      (show Nat.Coprime 2 3 by decide) (⟨⟨x, hxK⟩, hcore hz⟩ : pCore 2 K)
    simp only [Subgroup.orderOf_mk, hxG] at hp
    norm_num at hp
  have hfix : E ≤ centralizer ({(x : G)} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hxC y ((map_subtype_le A) hy))
  have hb := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hxG
    (fun he => hxK ((map_subtype_le A) he)) hfix hEc
  omega

omit [Finite G] in
/-- A strict S-orbit rules out normality in I. Containment S ≤ I suffices;
no ambient normality of L is asserted. -/
theorem relative_component_not_normal_of_strict_componentOrbit {L I S : Subgroup G}
    (hLI : L ≤ I) (hSI : S ≤ I) (hlt : L < componentOrbit L S) :
    ¬ (L.subgroupOf I).Normal := by
  intro hn
  have hnorm : I ≤ normalizer (L : Set G) := by
    exact (normal_subgroupOf_iff_le_normalizer hLI).mp hn
  have horbit : componentOrbit L S ≤ L := by
    apply iSup_le
    intro s
    exact (mem_normalizer_iff_map_conj_eq.mp (hnorm (hSI s.property))).le
  exact hlt.not_ge horbit

/-- The rank deduction at the start of 15.3.39. The odd-core input is the
clause of 15.3.33(3) for the actual ordinary component, and `h34` is the
positive-rank conclusion of 15.3.34. No concrete model rank is assumed. -/
theorem three_rank_one_of_strict_componentOrbit {L I S : Subgroup G}
    (hLI : L ≤ I) (hSI : S ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 (L.subgroupOf I) = ⊥)
    (hrankI : primeRank 3 I ≤ 2) (h34 : 1 ≤ primeRank 3 L)
    (hlt : L < componentOrbit L S) : primeRank 3 L = 1 := by
  have hnot := relative_component_not_normal_of_strict_componentOrbit hLI hSI hlt
  have hr : ¬ 2 ≤ primeRank 3 (L.subgroupOf I) :=
    fun h => hnot (normal_of_two_le_three_rank hL hodd h hrankI)
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)] at hr
  omega

omit [Finite G] in
/-- Extract the full nonnormal alternative of 1.2.1(3). The quotient
is transported by the actual equivalence `(L.subgroupOf I) ≃* L`, retaining
all four model alternatives. The Sylow subgroup is realized inside I. -/
theorem nonnormal_model_of_strict_componentOrbit {L I S : Subgroup G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (h121 : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel
          ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (hlt : L < componentOrbit L S) :
    (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) := by
  have hSI : S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  obtain ⟨hindex, hm⟩ := h121.resolve_left
    (relative_component_not_normal_of_strict_componentOrbit hLI hSI hlt)
  let e := subgroupOfEquivOfLe hLI
  exact ⟨hindex, hm.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm⟩

/-- Conditional assembly of the exact `hcompare` premise consumed by
`componentOrbit_eq_of_centerless_comparison_of_planeActors`.

`hmodels` is the full six-case rank-one deduction from literal 1.1.5(3),
including all model isomorphisms and action clauses. The source-input
theorem below supplies it from the proved model reduction. Only its trivial
two-core conclusion is consumed; no additional model certification is needed. -/
theorem centerless_comparison_of_rank_one_reduction
    (hmodels : ∀ (K : Type u) [Group K] [Finite K] [IsQuasisimple K]
      (α : MulAut K), Candidates.ComponentStructure.ModelAction115 K α →
        pPrimeCore 2 K = ⊥ → primeRank 3 K = 1 →
          Candidates.RankOneInitialModel K ∧ pCore 2 K = ⊥)
    {L I S M : Subgroup G} {z : G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I))
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) M z)
    (hSQT : IsStronglyQuasithin I) (h34 : 1 ≤ primeRank 3 L) :
    L < componentOrbit L S → center L = ⊥ ∧ primeRank 3 L = 1 := by
  intro hlt
  have hSI : S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have hr := three_rank_one_of_strict_componentOrbit hLI hSI hL h33.odd_core
    (hSQT 3 (by decide) (by decide)) h34 hlt
  let := hL.2
  obtain ⟨α, _, ha⟩ := h33.model_action
  have hrK : primeRank 3 (L.subgroupOf I) = 1 := by
    rwa [primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
  have hcore := (hmodels (L.subgroupOf I) α ha h33.odd_core hrK).2
  have hZ : center (L.subgroupOf I) = ⊥ :=
    eq_bot_iff.mpr ((center_le_twoCore_of_oddCore_eq_bot h33.odd_core).trans hcore.le)
  refine ⟨?_, hr⟩
  let e := subgroupOfEquivOfLe hLI
  apply eq_bot_iff.mpr
  intro x hx
  have he : e.symm x ∈ center (L.subgroupOf I) :=
    ((centerCongr e).symm ⟨x, hx⟩).property
  have he1 : e.symm x = 1 := by simpa only [hZ, mem_bot] using he
  exact mem_bot.mpr (e.symm.injective (he1.trans (map_one e.symm).symm))

/-- The center and rank comparison at the start of 15.3.39, from the genuine
earlier source conclusions. The complete six-case model reduction is proved,
not an additional premise. This is precisely the `hcompare` input of
`componentOrbit_eq_of_centerless_comparison_of_planeActors`.

The parent source assembly supplies `h33` for the selected ordinary component
(for example via `ComponentStructure.ordinary_component_structure`), the
local strong-quasithin bound, and the positive-rank clause of 15.3.34. -/
theorem centerless_comparison_of_source_inputs
    {L I S M : Subgroup G} {z : G}
    (hLI : L ≤ I) (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I))
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) M z)
    (hSQT : IsStronglyQuasithin I) (h34 : 1 ≤ primeRank 3 L) :
    L < componentOrbit L S → center L = ⊥ ∧ primeRank 3 L = 1 := by
  apply centerless_comparison_of_rank_one_reduction ?_ hLI P hP hL h33 hSQT h34
  intro K _ _ _ α
  exact Candidates.SignedReduction.RankOneModels.rankOneInitialModel_and_core α

end CFSG.Quasithin.Chapter15.Section03.RankTwo
