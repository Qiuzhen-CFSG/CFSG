module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.SylowNormalCenterIntersection
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The nontrivial intersection in 15.3.12

After the component orbit bound makes `Y₊` normalize `L`, the rank argument
is elementary. If `Y₊ ∩ L` were a two-group, an elementary subgroup of order
nine in `Y₊` would be disjoint from `L`. In a Sylow three-subgroup containing
that elementary subgroup, normality of `L` supplies a central element of
order three in `L`. Their join has order 27, contradicting the ambient
three-rank bound. Thus `O²(Y₊ ∩ L)` is nontrivial.

The local wrapper uses the exact theta identity from 15.3.11(6), the
component orbit bound from 1.2.1(3), and the three-rank bound supplied by
SQTK. No classification alternatives, exponent assumption on `Y₊`, or
nontrivial-intersection premise are used in this inference.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.12(1), printed pp.1124–1125 (PDF pp.1141–1142).
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
variable {G : Type*} [Group G] [Finite G]

private theorem rank_three_of_disjoint_normal (N E : Subgroup G) [N.Normal] [IsElementaryAbelian 3 E]
    (hN : 3 ∣ Nat.card N) (hE : Nat.card E = 9) (hd : Disjoint E N) :
    3 ≤ primeRank 3 G := by
  obtain ⟨P, hEP⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_le_sylow
  obtain ⟨x, hxc, hxne, hxN⟩ := P.exists_ne_one_mem_center_of_normal N hN
  let B := zpowers (x : G)
  have hBP : B ≤ (P : Subgroup G) := zpowers_le.mpr x.property
  have hBN : B ≤ N := zpowers_le.mpr hxN
  have hBne : B ≠ ⊥ := by
    intro h
    have hx1 : (x : G) = 1 := mem_bot.mp (h ▸ mem_zpowers (x : G))
    exact hxne (Subtype.ext hx1)
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hBne
  obtain ⟨n, hn, hc⟩ := (P.isPGroup'.to_le hBP).nontrivial_iff_card.mp inferInstance
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := B) 3
    (hc ▸ dvd_pow_self 3 (by omega))
  have hyG : orderOf (y : G) = 3 :=
    (orderOf_injective B.subtype B.subtype_injective y).trans hy
  have hcent : B ≤ centralizer (E : Set G) := by
    apply zpowers_le.mpr
    intro e he
    exact congrArg Subtype.val (mem_center_iff.mp hxc (⟨e, hEP he⟩ : P))
  have hyE : (y : G) ∉ E := by
    intro he
    have hy1 : (y : G) = 1 := hd.le_bot ⟨he, hBN y.property⟩
    simp [hy1] at hyG
  have hf : E ≤ centralizer ({(y : G)} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (hcent y.property e he)
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join (n := 2) E y hyG hyE hf hE


private theorem exists_elementary_nine (hG : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  let P : Sylow 3 G := Sylow.nonempty.some
  have hn : ¬ IsCyclic P := by
    intro hP
    have := P.primeRank_le_one_of_isCyclic hP
    omega
  obtain ⟨E, _, hc, hE⟩ := P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic
    (by decide) hn
  let : IsElementaryAbelian 3 E := hE
  exact ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map_subtype,
    (card_map_of_injective (P : Subgroup G).subtype_injective).trans hc⟩

private theorem not_twoGroup_intersection (N Y : Subgroup G) [N.Normal]
    (hN : 1 ≤ primeRank 3 N) (hY : 2 ≤ primeRank 3 Y)
    (hG : primeRank 3 G ≤ 2) : ¬ IsPGroup 2 (Y ⊓ N : Subgroup G) := by
  intro hp
  have hNdiv : 3 ∣ Nat.card N := by
    by_contra hn
    have := (PrimeRank.eq_zero_iff_not_dvd_card (G := N) (p := 3)).mpr hn
    omega
  obtain ⟨E, hE, hEcard⟩ := exists_elementary_nine hY
  let : IsElementaryAbelian 3 E := hE
  let B := E.map Y.subtype
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map_subtype
  have hBY : B ≤ Y := map_subtype_le E
  have hBcard : Nat.card B = 9 := (card_map_of_injective Y.subtype_injective).trans hEcard
  have hdis : Disjoint B N := by
    have hd := IsPGroup.disjoint_of_ne 3 2 (by decide) B (Y ⊓ N)
      (IsElementaryAbelian.isPGroup 3 B) hp
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    exact hd.le_bot ⟨hx.1, hBY hx.1, hx.2⟩
  have := rank_three_of_disjoint_normal N B hNdiv hBcard hdis
  omega

private theorem not_twoGroup_intersection_of_normalizes {Y L : Subgroup G}
    (hn : Y ≤ normalizer (L : Set G))
    (hY : primeRank 3 Y = 2) (hL : 1 ≤ primeRank 3 L)
    (hr : primeRank 3 (L ⊔ Y : Subgroup G) ≤ 2) :
    ¬ IsPGroup 2 (Y ⊓ L : Subgroup G) := by
  let H := L ⊔ Y
  let N := L.subgroupOf H
  let B := Y.subgroupOf H
  have hLH : L ≤ H := le_sup_left
  have hYH : Y ≤ H := le_sup_right
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  have hNr : 1 ≤ primeRank 3 N := by
    rw [Theory.GroupTheory.primeRank_equiv 3 (subgroupOfEquivOfLe hLH)]
    exact hL
  have hBr : 2 ≤ primeRank 3 B := by
    rw [Theory.GroupTheory.primeRank_equiv 3 (subgroupOfEquivOfLe hYH), hY]
  intro hp
  have hi : IsPGroup 2 (B ⊓ N : Subgroup H) :=
    hp.comap_of_injective H.subtype H.subtype_injective
  exact not_twoGroup_intersection N B hNr hBr hr hi

/-- Vanishing of the actual two-residual means that the intersection is a two-group. -/
theorem intersectionResidual_eq_bot_iff (Y L : Subgroup G) :
    intersectionResidual Y L = ⊥ ↔ IsPGroup 2 (Y ⊓ L : Subgroup G) := by
  rw [intersectionResidual, twoResidualAmbient_eq_map_pResidual]
  constructor
  · intro h
    have hr : pResidual 2 (Y ⊓ L : Subgroup G) = ⊥ :=
      (map_eq_bot_iff_of_injective _ (Y ⊓ L).subtype_injective).mp h
    have hp := isPGroup_quotient_pResidual (G := (Y ⊓ L : Subgroup G)) 2
    exact hp.of_equiv ((QuotientGroup.quotientMulEquivOfEq hr).trans
      QuotientGroup.quotientBot)
  · intro hp
    have hr : pResidual 2 (Y ⊓ L : Subgroup G) = ⊥ :=
      bot_unique (sInf_le ⟨inferInstance, hp.of_equiv QuotientGroup.quotientBot.symm⟩)
    rw [hr, Subgroup.map_bot]


/-- The short rank inference in 15.3.12(1), after component normalization. -/
theorem intersectionResidual_ne_bot_of_rank {Y L : Subgroup G}
    (hn : Y ≤ normalizer (L : Set G))
    (hY : primeRank 3 Y = 2) (hL : 1 ≤ primeRank 3 L)
    (hr : primeRank 3 (L ⊔ Y : Subgroup G) ≤ 2) :
    intersectionResidual Y L ≠ ⊥ := by
  intro h
  exact not_twoGroup_intersection_of_normalizes hn hY hL hr
    ((intersectionResidual_eq_bot_iff Y L).mp h)

/-- Nontriviality from the earlier local facts and the SQTK rank bound.
The containing component can be supplied through its inclusion and the
orbit bound; the rank inference itself works for any normalized subgroup. -/
theorem intersectionResidual_ne_bot_of_local_facts {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hY : primeRank 3 Y = 2) (hL : 1 ≤ primeRank 3 L)
    (hr : primeRank 3 I ≤ 2) : intersectionResidual Y L ≠ ⊥ := by
  have hYI : Y ≤ I := le_sup_left.trans hI.1.2
  have hn := normalizes_of_index_le_two hYI
    (htheta ▸ theta_isPPerfect (M ⊓ I)) hindex
  exact intersectionResidual_ne_bot_of_rank hn hY hL
    ((Theory.GroupTheory.primeRank_le_of_injective 3
      (inclusion (sup_le hLI hYI)) (inclusion_injective _)).trans hr)

open scoped Pointwise in
/-- The nontrivial intersection and core-product clauses for an actual C-component.
Normalization of the component by the local core is a separate remaining clause. -/
theorem intersection_ne_bot_and_core_product_le {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (hSM : S ≤ M)
    (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hYrank : primeRank 3 Y = 2) (hLrank : 1 ≤ primeRank 3 L)
    (hr : primeRank 3 I ≤ 2) :
    intersectionResidual Y L ≠ ⊥ ∧
      (L.pCoreIn 2 : Set G) * ((intersectionResidual Y L).pCoreIn 2 : Set G) ⊆
        (localCore Y S : Set G) :=
  ⟨intersectionResidual_ne_bot_of_local_facts hI htheta hLI hindex hYrank hLrank hr,
    core_product_le_of_local_facts hI hSM htheta hLI hL P hP hindex⟩

omit [Finite G] in
/-- The commutator used in the component-permutation argument lies in the actual local two-core. -/
theorem commutator_intersectionResidual_localCore_le (Y S L : Subgroup G) :
    ⁅intersectionResidual Y L, localCore Y S⁆ ≤ localCore Y S := by
  apply le_normalizer_iff_commutator_le_right.mp
  exact ((intersectionResidual_le Y L).trans inf_le_left).trans
    (le_sup_left.trans ((Y ⊔ S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (Y ⊔ S) (pCore 2 (Y ⊔ S : Subgroup G)))))

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection

end
