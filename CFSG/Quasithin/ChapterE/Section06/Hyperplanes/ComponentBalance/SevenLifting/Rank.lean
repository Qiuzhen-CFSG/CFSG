module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.Quasithin.Rank

/-!
# Three-rank and uniqueness of the exceptional seven components

Two disjoint three-cycles give three-rank at least two in A₇. The same lower
bound holds in a central three-cover: otherwise its Sylow three-subgroups
would be cyclic, and so would their images in A₇. No exponent-three assertion
about the whole Sylow subgroup of the cover is needed.

In an ambient group of three-rank at most two, every order-three element
centralizing a rank-two subgroup belongs to that subgroup. Distinct ordinary
components commute. An elementary nine in a second exceptional component
would therefore lie in its center, which has order at most three. This proves
uniqueness for both models without needing the alternatives of A.3.18.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252; compare the rank argument (*) in A.3.18, printed p.52.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Transport both exceptional model predicates through an actual isomorphism. -/
theorem IsSeven.of_equiv {H : Type*} [Group H] {L : Subgroup G} {J : Subgroup H}
    (hL : IsSeven L) (e : L ≃* J) : IsSeven J := by
  rcases hL with ha | hc
  · obtain ⟨f⟩ := ha
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨hq, ⟨c⟩, ⟨q⟩⟩ := hc
    let _ := hq
    have hz : (center L).map e.toMonoidHom = center J := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, ((centerCongr e).symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
    exact Or.inr ⟨IsQuasisimple.of_mulEquiv e, ⟨(centerCongr e).symm.trans c⟩,
      ⟨(QuotientGroup.congr (center L) (center J) e hz).symm.trans q⟩⟩

/-- Both genuine exceptional models have three-rank at least two. For a
central three-cover, cyclic Sylow three-subgroups would give a cyclic Sylow
subgroup in its A₇ quotient, contradicting the two disjoint three-cycles. -/
theorem IsSeven.two_le_primeRank {L : Subgroup G} (hL : IsSeven L) : 2 ≤ primeRank 3 L := by
  have hseven := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 7) (by decide)
  rcases hL with ha | hc
  · obtain ⟨e⟩ := ha
    rwa [primeRank_congr 3 e]
  · obtain ⟨_, _, ⟨e⟩⟩ := hc
    by_contra hn
    have hr : primeRank 3 L ≤ 1 := by omega
    let P : Sylow 3 L := Classical.choice inferInstance
    have hq := P.primeRank_quotient_le_one
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) (center L)
    rw [primeRank_congr 3 e] at hq
    omega

omit [Finite G] in
/-- The center is trivial for A₇ and cyclic of order three for the cover. -/
theorem IsSeven.card_center_le {L : Subgroup G} (hL : IsSeven L) : Nat.card (center L) ≤ 3 := by
  rcases hL with ha | hc
  · obtain ⟨e⟩ := ha
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by simp)]
    simp
  · obtain ⟨_, ⟨e⟩, _⟩ := hc
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]

private theorem elementaryNine_of_rank (h : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  let P : Sylow 3 G := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hr := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨E, _, hcard, he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let _ := he
  refine ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective] using hcard

private theorem mem_of_order_three_centralizing
    (hr : primeRank 3 G ≤ 2) {L : Subgroup G} (hL : 2 ≤ primeRank 3 L)
    {x : G} (hx : orderOf x = 3) (hc : x ∈ centralizer (L : Set G)) : x ∈ L := by
  obtain ⟨E, he, hcard⟩ := elementaryNine_of_rank hL
  let _ := he
  let A := E.map L.subtype
  let _ : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
  by_contra hn
  have hxa : x ∉ A := fun hx => hn (map_subtype_le E hx)
  have hfix : A ≤ centralizer ({x} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hc) a
      (map_subtype_le E ha))
  have hcardA : Nat.card A = 3 ^ 2 := by
    simpa only [A, card_map_of_injective L.subtype_injective] using hcard
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join A x hx hxa hfix hcardA
  omega

private theorem components_eq_of_rank (hr : primeRank 3 G ≤ 2) {L J : Subgroup G}
    (hL : IsComponent G L) (hJ : IsComponent G J)
    (hrL : 2 ≤ primeRank 3 L) (hrJ : 2 ≤ primeRank 3 J)
    (hzJ : Nat.card (center J) ≤ 3) : L = J := by
  by_contra hn
  have hc : L ≤ centralizer (J : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hJ hn)
  obtain ⟨E, he, hcard⟩ := elementaryNine_of_rank hrJ
  let _ := he
  have hEZ : E ≤ center J := by
    intro x hx
    have hxG : (x : G) ∈ L := by
      by_cases hx1 : x = 1
      · simp [hx1]
      have ho : orderOf x = 3 := by
        have hp : x ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
        exact (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
          (orderOf_dvd_of_pow_eq_one hp) |>.resolve_left
            (fun h => hx1 (orderOf_eq_one_iff.mp h))
      apply mem_of_order_three_centralizing hr hrL
        ((orderOf_injective J.subtype J.subtype_injective x).trans ho)
      exact le_centralizer_iff.mp hc x.property
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((mem_centralizer_iff.mp (hc hxG)) y y.property)
  have hbound := (card_le_of_le hEZ).trans hzJ
  rw [hcard] at hbound
  omega

/-- The rank argument includes both A₇ and its perfect central three-cover. -/
theorem seven_components_eq (hr : primeRank 3 G ≤ 2) {L J : Subgroup G}
    (hL : IsComponent G L) (hJ : IsComponent G J)
    (hsL : IsSeven L) (hsJ : IsSeven J) : L = J :=
  components_eq_of_rank hr hL hJ hsL.two_le_primeRank hsJ.two_le_primeRank
    hsJ.card_center_le

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
