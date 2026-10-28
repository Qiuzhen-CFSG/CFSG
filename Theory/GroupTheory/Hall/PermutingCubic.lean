module
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Cubics in the normal intersection of a permuting odd actor

An odd subgroup permuting with a two-subgroup is Hall in their join.
Restrict this Hall subgroup to a normalized intersection. If three divides
the intersection order, Cauchy's theorem supplies a subgroup of order three
inside the original odd actor and the original normalized subgroup.

Source application: Aschbacher--Smith 5.1.13, printed p.636. The binary
triality application retains the literal quotient and component intersection
in Theory.SpecificGroups.Triality.BinarySolvableCubic.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

private theorem odd_hall_of_permuting (A S : Subgroup G)
    (ho : Odd (Nat.card A)) (hs : IsPGroup 2 S)
    (hperm : (A : Set G) * S = (S : Set G) * A) :
    IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (A ⊔ S)) := by
  have hd : Disjoint A S := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := hs.exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  have hc := card_set_mul_mul_card_inf A S
  rw [←coe_sup_of_set_mul_comm A S hperm] at hc
  change Nat.card (A ⊔ S : Subgroup G) * Nat.card (A ⊓ S : Subgroup G) =
    Nat.card A * Nat.card S at hc
  rw [hd.eq_bot,card_bot,mul_one] at hc
  have hi : (A.subgroupOf (A ⊔ S)).index = Nat.card S := by
    have hh := (A.subgroupOf (A ⊔ S)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ A ⊔ S from le_sup_left)).toEquiv,hc] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  refine ⟨?_,?_⟩
  · intro p hp he
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ A ⊔ S from le_sup_left)).toEquiv] at hp
    exact ho.not_two_dvd_nat (he ▸ hp)
  · intro p hp hp2
    rw [hi] at hp
    obtain ⟨k,hk⟩ := hs.exists_card_eq
    rw [hk] at hp
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hp)

/-- Hall restriction retains a genuine cubic in the original odd actor
inside the same normalized subgroup. -/
theorem exists_cubic_in_intersection (A S C : Subgroup G)
    (ho : Odd (Nat.card A)) (hs : IsPGroup 2 S)
    (hperm : (A : Set G) * S = (S : Set G) * A)
    (hn : A ⊔ S ≤ normalizer (C : Set G))
    (hthree : 3 ∣ Nat.card ((A ⊔ S) ⊓ C : Subgroup G)) :
    ∃ D : Subgroup G, D ≤ A ∧ D ≤ C ∧ Nat.card D = 3 := by
  let I := (A ⊔ S) ⊓ C
  have hAI : A ≤ normalizer (I : Set G) :=
    (le_inf (le_sup_left.trans (A ⊔ S).le_normalizer) (le_sup_left.trans hn)).trans
      inf_normalizer_le_normalizer_inf
  have hh := OddHall.hall_restrict_of_normalizes (odd_hall_of_permuting A S ho hs hperm)
    (show A ≤ A ⊔ S from le_sup_left) (show I ≤ A ⊔ S from inf_le_left) hAI
  have hd : 3 ∣ Nat.card (A.subgroupOf I) := by
    have hc := (A.subgroupOf I).card_mul_index
    have hd : 3 ∣ Nat.card (A.subgroupOf I) * (A.subgroupOf I).index := hc.symm ▸ hthree
    exact (Nat.prime_three.dvd_mul.mp hd).resolve_right (fun he =>
      hh.p_in_pi_of_p_dvd_index ⟨3,Nat.prime_three⟩ he (by change (3 : ℕ) ≠ 2; decide))
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := A.subgroupOf I) 3 hd
  let f := I.subtype.comp (A.subgroupOf I).subtype
  have hf : Function.Injective f := I.subtype_injective.comp (A.subgroupOf I).subtype_injective
  refine ⟨(zpowers z).map f,?_,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · rintro _ ⟨x,_,rfl⟩
    exact x.val.property.2
  · rw [card_map_of_injective hf,Nat.card_zpowers,hz]

end Subgroup.OddHall
