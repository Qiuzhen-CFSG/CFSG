module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer

/-!
# Faithful two-group actions and full odd-primary centralizers

A nontrivial two-group acting faithfully on a normal p-group contains an
involution with nontrivial action. Every p-subgroup of its full centralizer
lies in the centralizer of this involution, hence is cyclic by A.1.31(1).
The odd-prime rank hypothesis remains on the original source of a surjection.

The actual cyclic action in Aschbacher--Smith 14.1.17(4) is a special case.
-/

public section
open Subgroup
namespace Theory.GroupTheory
universe u v
variable {K : Type u} [Group K] [Finite K] {G : Type v} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

theorem cyclic_pSubgroup_in_two_centralizer_of_faithful
    (hp : Odd p) (f : K →* G) (hf : Function.Surjective f) (hrank : primeRank p K ≤ 2)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hne : A ≠ ⊥)
    (hfaith : Function.Injective ((MulAut.conjNormal : G →* MulAut P).domRestrict A))
    (R : Subgroup G) (hR : IsPGroup p R) (hRA : R ≤ centralizer (A : Set G)) :
    IsCyclic R := by
  obtain ⟨k,hk⟩ := hA.exists_card_eq
  have hcard : 1 < Nat.card A := A.one_lt_card_iff_ne_bot.mpr hne
  have hkne : k ≠ 0 := by intro he; rw [he,pow_zero] at hk; omega
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2
    (by rw [hk]; exact dvd_pow_self 2 hkne : 2 ∣ Nat.card A)
  have htG : orderOf (t : G) = 2 := (orderOf_injective A.subtype A.subtype_injective t).trans ht
  have hnon : (t : G) ∉ centralizer (P : Set G) := by
    intro hc
    have he : (MulAut.conjNormal : G →* MulAut P) t = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change (t : G) * x * (t : G)⁻¹ = x
      rw [←hc x x.property,mul_assoc,mul_inv_cancel,mul_one]
    have htone : t = 1 := hfaith (he.trans (map_one _).symm)
    norm_num [htone] at ht
  exact cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two hp f hf hrank
    P hP t htG hnon R hR
    (hRA.trans (centralizer_le (Set.singleton_subset_iff.mpr t.property)))

end Theory.GroupTheory
