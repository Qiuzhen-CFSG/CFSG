module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.NormNum

/-!
# A Sylow-seven obstruction to index four

If a group has order 6048 and no involution centralizer has order divisible
by seven, it has no normal subgroup of index four. The centralizer of any
subgroup of order seven has odd order. Its normalizer acts on the cyclic
seven-group, so its order is not divisible by four. Frattini's argument for
a hypothetical normal subgroup of index four gives the contradiction.

This is the final elementary obstruction in Suzuki (1965), Section II,
Lemma 3, specialized to degree 28. No simplicity or transfer conclusion is
assumed here.
-/

namespace Subgroup

/-- An involution-centralizer condition bounds the two-part of the normalizer
of a subgroup of order seven. -/
public theorem not_four_dvd_card_normalizer_seven
    {G : Type*} [Group G] [Finite G]
    (hcentral : ∀ j : G, orderOf j = 2 →
      ¬ 7 ∣ Nat.card (centralizer ({j} : Set G)))
    (P : Subgroup G) (hP : Nat.card P = 7) :
    ¬ 4 ∣ Nat.card (normalizer (P : Set G)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hc : ¬ 2 ∣ Nat.card (centralizer (P : Set G)) := by
    intro heven
    obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 2 heven
    have hjG : orderOf (j : G) = 2 := (orderOf_coe j).trans hj
    apply hcentral j hjG
    have hle : P ≤ centralizer ({(j : G)} : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp j.property) x hx)
    exact hP ▸ card_dvd_of_le hle
  let f := P.normalizerMonoidHom
  have hAut : Nat.card (MulAut P) = 6 := by
    rw [IsCyclic.card_mulAut, hP]
    decide
  have hrange : Nat.card f.range ∣ 6 := hAut ▸ f.range.card_subgroup_dvd_card
  have hker : Nat.card f.ker = Nat.card (centralizer (P : Set G)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set G))).toEquiv]
  have hodd : Odd (Nat.card f.ker) := by
    rw [hker, Nat.odd_iff]
    omega
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  intro hfour
  have hdiv : 4 ∣ Nat.card f.range := by
    apply (hodd.coprime_two_left.pow_left 2).dvd_of_dvd_mul_left
    simpa only [hprod] using hfour
  have := hdiv.trans hrange
  norm_num at this

/-- The involution-centralizer condition rules out a normal subgroup of
index four in a group of order 6048. -/
public theorem index_ne_four_of_card_6048_of_seven_free_involution_centralizers
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 6048)
    (hcentral : ∀ j : G, orderOf j = 2 →
      ¬ 7 ∣ Nat.card (centralizer ({j} : Set G)))
    (N : Subgroup G) [N.Normal] : N.index ≠ 4 := by
  intro hindex
  have hN : Nat.card N = 1512 := by
    have hc := N.card_mul_index
    rw [hG, hindex] at hc
    omega
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 N := default
  have hP : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, hN]
    rw [show 1512 = 2 ^ 3 * 3 ^ 3 * 7 from by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_pow, Nat.factorization_pow,
      Nat.prime_two.factorization, Nat.prime_three.factorization,
      (show Nat.Prime 7 by decide).factorization]
    norm_num
  let R : Subgroup G := (P : Subgroup N).map N.subtype
  have hR : Nat.card R = 7 := by
    rw [card_map_of_injective N.subtype_injective]
    exact hP
  have hsup : normalizer (R : Set G) ⊔ N = ⊤ := P.normalizer_sup_eq_top
  have hrel : N.relIndex (normalizer (R : Set G)) = 4 := by
    rw [← relIndex_sup_right, hsup, relIndex_top_right, hindex]
  have hfour : 4 ∣ Nat.card (normalizer (R : Set G)) :=
    hrel ▸ N.relIndex_dvd_card (normalizer (R : Set G))
  exact not_four_dvd_card_normalizer_seven hcentral R hR hfour

end Subgroup
