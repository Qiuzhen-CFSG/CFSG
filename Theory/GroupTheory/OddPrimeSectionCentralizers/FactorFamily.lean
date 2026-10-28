module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Commuting odd-prime factors in rank-two sections

An involution moving a normal p-subgroup has cyclic p-subgroups in its full
centralizer. Two disjoint nontrivial commuting p-groups cannot generate a
cyclic group. Thus a family of independent p-factors, all but one centralized
by that involution, has at most two members.

The rank hypothesis remains on the original group covering the section.
Source: Aschbacher--Smith A.1.31(1), applied in 15.1.2, p.1084.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]

omit [Finite G] in
private theorem not_cyclic_sup_of_disjoint_nontrivial_pGroups
    (A B : Subgroup G) (hA : IsPGroup p A) (hB : IsPGroup p B)
    (hneA : A ≠ ⊥) (hneB : B ≠ ⊥) (hd : Disjoint A B)
    (hc : A ≤ centralizer (B : Set G)) : ¬ IsCyclic (A ⊔ B : Subgroup G) := by
  intro hcyc
  let := hcyc
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  have hpA : p ∣ Nat.card A := hA.card_eq_or_dvd.resolve_left
    (fun he => hneA (card_eq_one.mp he))
  have hpB : p ∣ Nat.card B := hB.card_eq_or_dvd.resolve_left
    (fun he => hneB (card_eq_one.mp he))
  have hcAB : IsCyclic (A × B) := isCyclic_of_injective e.toMonoidHom e.injective
  have hcop := (Group.isCyclic_prod_iff.mp hcAB).2.2
  exact (Fact.out : p.Prime).not_dvd_one (hcop ▸ Nat.dvd_gcd hpA hpB)

/-- Only one member of a disjoint commuting p-family can centralize an
involution that moves a normal p-subgroup in a rank-two section. -/
theorem commuting_pFamily_away_index_subsingleton
    (hp : Odd p) (f : H →* G) (hf : Function.Surjective f)
    (hrank : primeRank p H ≤ 2)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (t : G) (ht : orderOf t = 2) (htP : t ∉ centralizer (P : Set G))
    {ι : Type*} (R : ι → Subgroup G) (i : ι)
    (hR : ∀ j, IsPGroup p (R j)) (hne : ∀ j, R j ≠ ⊥)
    (hdis : Pairwise (fun j k => Disjoint (R j) (R k)))
    (hcomm : Pairwise (fun j k => R j ≤ centralizer (R k : Set G)))
    (hfix : ∀ j, j ≠ i → R j ≤ centralizer ({t} : Set G)) :
    ∀ j k, j ≠ i → k ≠ i → j = k := by
  intro j k hj hk
  by_contra hneJK
  have hRsup : IsPGroup p (R j ⊔ R k : Subgroup G) := by
    obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
      (R j) (R k) (hdis hneJK) (hcomm hneJK)
    obtain ⟨a, ha⟩ := (hR j).exists_card_eq
    obtain ⟨b, hb⟩ := (hR k).exists_card_eq
    have hab : IsPGroup p (R j × R k) := IsPGroup.of_card (n := a + b)
      (by rw [Nat.card_prod, ha, hb, pow_add])
    exact hab.of_equiv e
  have hcyc := cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    hp f hf hrank P hP t ht htP (R j ⊔ R k) hRsup (sup_le (hfix j hj) (hfix k hk))
  exact not_cyclic_sup_of_disjoint_nontrivial_pGroups
    (R j) (R k) (hR j) (hR k) (hne j) (hne k) (hdis hneJK) (hcomm hneJK) hcyc

theorem commuting_pFamily_card_le_two
    (hp : Odd p) (f : H →* G) (hf : Function.Surjective f)
    (hrank : primeRank p H ≤ 2)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (t : G) (ht : orderOf t = 2) (htP : t ∉ centralizer (P : Set G))
    {ι : Type*} [Finite ι] (R : ι → Subgroup G) (i : ι)
    (hR : ∀ j, IsPGroup p (R j)) (hne : ∀ j, R j ≠ ⊥)
    (hdis : Pairwise (fun j k => Disjoint (R j) (R k)))
    (hcomm : Pairwise (fun j k => R j ≤ centralizer (R k : Set G)))
    (hfix : ∀ j, j ≠ i → R j ≤ centralizer ({t} : Set G)) :
    Nat.card ι ≤ 2 := by
  classical
  let := Fintype.ofFinite ι
  have huniq := commuting_pFamily_away_index_subsingleton hp f hf hrank P hP t ht htP
    R i hR hne hdis hcomm hfix
  by_contra hn
  have hlt : 2 < Fintype.card ι := by simpa only [Nat.card_eq_fintype_card] using Nat.lt_of_not_ge hn
  obtain ⟨a,b,c,hab,hac,hbc⟩ := Fintype.two_lt_card_iff.mp hlt
  by_cases hai : a = i
  · subst a
    exact hbc (huniq b c hab.symm hac.symm)
  by_cases hbi : b = i
  · subst b
    exact hac (huniq a c hab hbc.symm)
  exact hab (huniq a b hai hbi)
end Theory.GroupTheory

