module
public import Theory.GroupTheory.InvolutionCentralizerRank.FusionCyclic
public import Theory.GroupTheory.InvolutionCentralizerRank.FusionUniqueFour
public import Theory.GroupTheory.InvolutionCentralizerRank.FusionCentralFour
public import Theory.ElementaryAbelian.FixedOrderGeneration

/-!
# Rank-two involution centralizers in finite simple groups

A finite simple centerless group with an involution centralizer of two-rank
at most two has only one class of involutions. The rank reduction is GLS2
15.17(i). For the resulting rank-two Sylow subgroup, no normal four gives
a cyclic subgroup of index at most two; multiple normal fours give D8.
Thompson transfer handles these cases. A unique normal four with center
omega of order two is handled by the square-root weak-closure argument and
Z*. If central omega has order four, its three involutions and Z* force one
class directly.

The contrapositive produces an actual elementary subgroup of order eight in
the centralizer of each involution as soon as two ambient involution classes
are distinct. This is the precise source input for the ZD Section 16 argument.

Source: GLS, volume 4, Chapter 1, Lemma 4.10, specialized to finite simple
centerless groups; GLS, volume 2, 10.11 and 15.16–17. Simplicity supplies
trivial odd core in the applied Z* theorem.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The global rank-two fusion theorem on the simple source domain. -/
theorem isConj_involutions_of_rank_two
    (S : Sylow 2 G) (hcenter : center G = ⊥)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  classical
  obtain ⟨s, hs⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have hs1 : s ≠ 1 := by
    intro h
    have he : x = 1 := isConj_one_left.mp (by simpa [h] using hs)
    simp [he] at hx
  let : Nontrivial S := ⟨⟨s, 1, hs1⟩⟩
  rcases S.isPGroup'.card_omega_one_center_eq_two_or_four hrank with hZ | hZ
  · by_cases hfour : ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4
    · obtain ⟨E, hEn, hEe, hE⟩ := hfour
      let : E.Normal := hEn
      let : IsElementaryAbelian 2 E := hEe
      by_cases hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = E
      · exact S.isConj_involutions_of_unique_normal_four hcenter hno hrank hZ E hE hunique x y hx hy
      · push Not at hunique
        obtain ⟨F, hFn, hFe, hF, hne⟩ := hunique
        let : F.Normal := hFn
        let : IsElementaryAbelian 2 F := hFe
        exact S.isConj_involutions_of_distinct_normal_fours hno hrank E F hE hF hne.symm x y hx hy
    · exact S.isConj_involutions_of_no_normal_four hno hfour x y hx hy
  · exact S.isConj_involutions_of_omega_center_card_four hcenter hrank hZ hx hy
end Sylow

/-- GLS4 4.10 for finite simple centerless groups, with a weak inequality
allowing direct use of its contrapositive. -/
theorem isConj_involutions_of_rank_two_centralizer_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcenter : center G = ⊥)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (u : G) (hu : orderOf u = 2) (hC : primeRank 2 (centralizer {u}) ≤ 2)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  let S : Sylow 2 G := default
  have hr := S.primeRank_two_le_two_of_involution_centralizer hno u hu hC
  apply S.isConj_involutions_of_rank_two hcenter hno _ x y hx hy
  intro A hA
  have hc := (primeRank_le_iff_elementary_card_le S).mp hr A hA
  change Nat.card A ≤ 2 ^ 2 at hc
  omega

/-- Distinct ambient involution classes force rank at least three in every
involution centralizer on the simple source domain. -/
theorem primeRank_centralizer_ge_three_of_nonconjugate_involutions
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcenter : center G = ⊥)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : ¬ IsConj x y)
    (u : G) (hu : orderOf u = 2) : 3 ≤ primeRank 2 (centralizer {u}) := by
  by_contra! hc
  exact hxy (isConj_involutions_of_rank_two_centralizer_of_simple hcenter hno u hu (by omega) x y hx hy)

/-- The actual elementary-eight centralizer input used in the ZD source
argument. Its subgroup is intrinsic to the original marked centralizer. -/
theorem exists_elementary_eight_in_centralizer_of_nonconjugate_involutions
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcenter : center G = ⊥)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : ¬ IsConj x y)
    (u : G) (hu : orderOf u = 2) :
    ∃ E : Subgroup (centralizer {u}), IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
  have hr := primeRank_centralizer_ge_three_of_nonconjugate_involutions hcenter hno x y hx hy hxy u hu
  have hlarge : ∃ V : Subgroup (centralizer {u}), IsElementaryAbelian 2 V ∧ 4 < Nat.card V := by
    by_contra! hn
    have hb := (primeRank_le_iff_elementary_card_le (p := 2) (n := 2) (centralizer {u})).mpr hn
    change primeRank 2 (centralizer {u}) ≤ 2 at hb
    omega
  obtain ⟨V, hVe, hV⟩ := hlarge
  let : IsElementaryAbelian 2 V := hVe
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra! hlt
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 2 by omega)
    omega
  have h8 : 8 ≤ Nat.card V := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn3
  obtain ⟨E, _, hE, hEc, _⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem V
    (n := 3) (by decide) h8 1 V.one_mem
  exact ⟨E, hE, hEc⟩

private theorem no_normal_index_two_of_simple_centerless
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (hcenter : center G = ⊥) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hindex
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa [hbot] using hindex
    let : IsCyclic G := isCyclic_of_prime_card hcard
    let : CommGroup G := IsCyclic.commGroup
    have he : (⊤ : Subgroup G) = ⊥ := (CommGroup.center_eq_top (G := G)).symm.trans hcenter
    have hone (g : G) : g = 1 := Subgroup.mem_bot.mp (he ▸ Subgroup.mem_top g)
    let : Subsingleton G := ⟨fun a b => (hone a).trans (hone b).symm⟩
    have hc := Nat.card_unique (α := G)
    omega
  · simp [htop] at hindex

/-- Fully specialized simple-group source consequence: every involution
centralizer contains an actual elementary eight when two involution classes
differ. The no-index-two hypothesis is derived from simplicity and trivial
center. -/
theorem exists_elementary_eight_in_centralizer_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcenter : center G = ⊥)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : ¬ IsConj x y)
    (u : G) (hu : orderOf u = 2) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ E ≤ centralizer {u} := by
  obtain ⟨E, hE, hEc⟩ := exists_elementary_eight_in_centralizer_of_nonconjugate_involutions
    hcenter (no_normal_index_two_of_simple_centerless hcenter) x y hx hy hxy u hu
  let : IsElementaryAbelian 2 E := hE
  exact ⟨E.map (centralizer {u}).subtype, IsElementaryAbelian.map _,
    (card_map_of_injective (centralizer {u}).subtype_injective).trans hEc, map_subtype_le _⟩
