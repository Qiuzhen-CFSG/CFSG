module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Odd orders inverted by a dihedral pair

If an involution t inverts x, the pair t and x t x⁻¹ contains x⁻².
For x of odd order this has the same order as x. Thus a pair subgroup
of order six, ten or twelve forces nonidentity inverted odd elements
to have order three or five. A moved normal p-subgroup supplies an
inverted nonidentity commutator, excluding movement for other odd primes.

Source application: Aschbacher--Smith, proof of 12.6.26, pp.831--832.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem inverter_product (t x : G) (ht : t^2=1)
    (hi : t*x*t⁻¹=x⁻¹) : t * (x*t*x⁻¹) = (x^2)⁻¹ := by
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht)
  calc
    t * (x*t*x⁻¹) = (t*x*t⁻¹)*x⁻¹ := by rw [hti]; group
    _ = (x^2)⁻¹ := by rw [hi]; group

/-- A dihedral pair order bound controls odd elements inverted by its involution. -/
theorem inverted_odd_order_of_pair_card
    (B : Subgroup G) (t x : G) (ht : t^2=1) (htB : t ∈ B)
    (hcB : x*t*x⁻¹ ∈ B) (hi : t*x*t⁻¹=x⁻¹)
    (ho : Odd (orderOf x)) (hx : x ≠ 1)
    (hB : ¬ IsPGroup 2 B → Nat.card B = 6 ∨ Nat.card B = 10 ∨ Nat.card B = 12) :
    orderOf x=3 ∨ orderOf x=5 := by
  have hm : (x^2)⁻¹ ∈ B := inverter_product t x ht hi ▸ B.mul_mem htB hcB
  let y : B := ⟨(x^2)⁻¹,hm⟩
  have he : orderOf y=orderOf x := by
    rw [←Subgroup.orderOf_coe, orderOf_inv,ho.coprime_two_right.orderOf_pow]
  have hy : y ≠ 1 := by
    intro h
    have hh : orderOf x=1 := by rw [←he,h,orderOf_one]
    exact hx (orderOf_eq_one_iff.mp hh)
  have hn : ¬ IsPGroup 2 B := fun hp => ho.not_two_dvd_nat (he ▸ hp.dvd_orderOf hy)
  have hd : orderOf x ∣ Nat.card B := he ▸ orderOf_dvd_natCard y
  have hne : orderOf x ≠ 1 := fun he => hx (orderOf_eq_one_iff.mp he)
  rcases hB hn with hc | hc | hc
  · rw [hc] at hd
    have h3 : orderOf x ∣ 3 := ho.coprime_two_right.dvd_of_dvd_mul_left hd
    exact Or.inl ((Nat.dvd_prime (by decide)).mp h3 |>.resolve_left hne)
  · rw [hc] at hd
    have h5 : orderOf x ∣ 5 := ho.coprime_two_right.dvd_of_dvd_mul_left hd
    exact Or.inr ((Nat.dvd_prime (by decide)).mp h5 |>.resolve_left hne)
  · rw [hc] at hd
    have h6 : orderOf x ∣ 6 := ho.coprime_two_right.dvd_of_dvd_mul_left hd
    have h3 : orderOf x ∣ 3 := ho.coprime_two_right.dvd_of_dvd_mul_left h6
    exact Or.inl ((Nat.dvd_prime (by decide)).mp h3 |>.resolve_left hne)

/-- Restricting inverted odd orders to three and five excludes all other odd cores. -/
theorem centralizes_pGroup_of_inverted_orders
    (t : G) (ht : t^2=1)
    (horders : ∀ x : G, x ≠ 1 → Odd (orderOf x) → t*x*t⁻¹=x⁻¹ →
      orderOf x=3 ∨ orderOf x=5)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) :
    t ∈ centralizer (R : Set G) := by
  intro r hr
  by_contra hn
  let x := t*r*t⁻¹*r⁻¹
  have hxR : x ∈ R := R.mul_mem (Subgroup.Normal.conj_mem inferInstance r hr t) (R.inv_mem hr)
  have hx : x ≠ 1 := by
    intro he
    have he' : t*r*t⁻¹=r := mul_inv_eq_one.mp he
    exact hn (mul_inv_eq_iff_eq_mul.mp he').symm
  have hi : t*x*t⁻¹=x⁻¹ := by
    have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht)
    have htt : t*t=1 := by simpa [pow_two] using ht
    dsimp [x]
    rw [_root_.mul_inv_rev,_root_.mul_inv_rev,_root_.mul_inv_rev,inv_inv,inv_inv,hti]
    simp only [←mul_assoc,htt,one_mul]
  have ho : Odd (orderOf x) := by
    obtain ⟨k,hk⟩ := hR.exists_orderOf_eq_pow (⟨x,hxR⟩ : R)
    rw [←Subgroup.orderOf_coe] at hk
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have hd : p ∣ orderOf x := by
    exact (Subgroup.orderOf_coe (⟨x,hxR⟩ : R)).symm ▸
      hR.dvd_orderOf (fun he => hx (congrArg Subtype.val he))
  rcases horders x hx ho hi with h | h
  · rw [h] at hd
    exact hp3 ((Nat.dvd_prime (by decide)).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one)
  · rw [h] at hd
    exact hp5 ((Nat.dvd_prime (by decide)).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one)
end Theory.GroupTheory
