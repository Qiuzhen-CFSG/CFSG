module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.TwoPrimeSolvable
public import FeitThompson.FinalTheorem

/-!
# Element orders forced by two C-components

Distinct C-components give disjoint commuting simple images modulo the
solvable radical. Burnside's two-prime theorem supplies a prime other than
two and three in each image, and the odd-order theorem supplies involutions.
Their direct product produces mixed element orders. These orders lift to
the original group by taking a suitable power of a quotient preimage.

The resulting numerical obstruction is used for the Mathieu overgroups in
Aschbacher--Smith A.3.12 and 1.2.8(1), printed pp.47--48 and 506. It retains
the solvable radical; no splitting of that radical is required.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem lift_order {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f) (x : H) :
    ∃ g : G, orderOf g = orderOf x := by
  obtain ⟨g, rfl⟩ := hf x
  exact ⟨g ^ (orderOf g / orderOf (f g)),
    orderOf_pow_orderOf_div (orderOf_pos g).ne' (orderOf_map_dvd f g)⟩

private theorem pair_spectrum {B C : Subgroup G} (hB : B.IsCComponent)
    (hC : C.IsCComponent) (hne : B ≠ C)
    (a : B.map (QuotientGroup.mk' (solvableRadical G)))
    (b : C.map (QuotientGroup.mk' (solvableRadical G))) :
    ∃ g : G, orderOf g = Nat.lcm (orderOf a) (orderOf b) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  have hA := hB.map_quotient (solvableRadical G)
  have hD := hC.map_quotient (solvableRadical G)
  have hr := solvableRadical_quotient_solvableRadical (G := G)
  have hn : B.map q ≠ C.map q := fun he => hne (hB.eq_of_map_quotient_eq hC _ he)
  obtain ⟨e, _⟩ := hA.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hr
    (hA.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hr hD hn)
  obtain ⟨g, hg⟩ := lift_order q (QuotientGroup.mk'_surjective _) (e (a,b) : G ⧸ _)
  refine ⟨g, ?_⟩
  rw [hg, Subgroup.orderOf_coe, e.orderOf_eq, Prod.orderOf_mk]

private theorem component_even {B : Subgroup G} (hB : B.IsCComponent) : 2 ∣ Nat.card B := by
  by_contra ho
  exact hB.not_isSolvable (odd_order_theorem B (Nat.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using ho)))

private theorem cross_prime {B C : Subgroup G} (hB : B.IsCComponent)
    (hC : C.IsCComponent) (hne : B ≠ C) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : p ∣ Nat.card (B.map (QuotientGroup.mk' (solvableRadical G)))) :
    ∃ g : G, orderOf g = 2 * p := by
  let := Fact.mk hp
  have hD := hC.map_quotient (solvableRadical G)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 (component_even hD)
  obtain ⟨g, hg⟩ := pair_spectrum hB hC hne a b
  refine ⟨g, ?_⟩
  rw [ha, hb, hp.coprime_iff_not_dvd.mpr (fun hd => hp2
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)) |>.lcm_eq_mul] at hg
  simpa only [Nat.mul_comm] using hg


private theorem prime_outside_two_three {B : Subgroup G} (hB : B.IsCComponent) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card B ∧ p ≠ 2 ∧ p ≠ 3 := by
  by_contra h
  apply hB.not_isSolvable
  apply isSolvable_of_prime_dvd_card_eq_two_or_prime B Nat.prime_three
  intro p hp hd
  by_contra hne
  exact h ⟨p, hp, hd, fun h2 => hne (Or.inl h2), fun h3 => hne (Or.inr h3)⟩

/-- Distinct C-components force two odd primes outside three, their product in
the group order, and the corresponding mixed element orders. -/
theorem IsCComponent.exists_prime_pair_of_ne {B C : Subgroup G} (hB : B.IsCComponent)
    (hC : C.IsCComponent) (hne : B ≠ C) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ r ≠ 2 ∧ r ≠ 3 ∧
      p * r ∣ Nat.card G ∧
      (∃ g : G, orderOf g = Nat.lcm p r) ∧
      (∃ g : G, orderOf g = 2 * p) ∧ (∃ g : G, orderOf g = 2 * r) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  have hA := hB.map_quotient (solvableRadical G)
  have hD := hC.map_quotient (solvableRadical G)
  obtain ⟨p,hp,hpd,hp2,hp3⟩ := prime_outside_two_three hA
  obtain ⟨r,hr,hrd,hr2,hr3⟩ := prime_outside_two_three hD
  have hrad := solvableRadical_quotient_solvableRadical (G := G)
  have hn : B.map q ≠ C.map q := fun he => hne (hB.eq_of_map_quotient_eq hC _ he)
  obtain ⟨e, _⟩ := hA.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hrad
    (hA.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hrad hD hn)
  have hprod : Nat.card (B.map q) * Nat.card (C.map q) ∣ Nat.card G := by
    rw [← Nat.card_prod, Nat.card_congr e.toEquiv]
    exact (card_subgroup_dvd_card _).trans (card_quotient_dvd_card _)
  refine ⟨p,r,hp,hr,hp2,hp3,hr2,hr3,(Nat.mul_dvd_mul hpd hrd).trans hprod, ?_,
    cross_prime hB hC hne hp hp2 hpd, cross_prime hC hB hne.symm hr hr2 hrd⟩
  let := Fact.mk hp
  let := Fact.mk hr
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p hpd
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' r hrd
  simpa only [ha,hb] using pair_spectrum hB hC hne a b

end Subgroup

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- An element of order twice a prime exhibits that prime in an involution centralizer. -/
theorem exists_involution_centralizer_prime_dvd_of_orderOf (g : G) {p : ℕ} (hp : p.Prime) (hg : orderOf g = 2*p) :
    ∃ t : G, orderOf t = 2 ∧ p ∣ Nat.card (centralizer ({t} : Set G)) := by
  have ht : orderOf (g ^ p) = 2 := by
    rw [orderOf_pow_of_dvd hp.ne_zero (hg ▸ dvd_mul_left p 2), hg,
      Nat.mul_div_cancel _ hp.pos]
  refine ⟨g ^ p, ht, ?_⟩
  let x : centralizer ({g ^ p} : Set G) :=
    ⟨g, mem_centralizer_singleton_iff.mpr ((Commute.refl g).pow_left p).eq.symm⟩
  have hx : orderOf x = 2*p := (orderOf_coe x).symm.trans hg
  exact (dvd_mul_left p 2).trans (hx ▸ orderOf_dvd_natCard x)

end Theory.GroupTheory
