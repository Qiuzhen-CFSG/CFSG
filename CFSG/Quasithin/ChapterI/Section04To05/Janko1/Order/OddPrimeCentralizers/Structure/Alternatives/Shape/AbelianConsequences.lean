module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.Shape.FourAction

/-!
# Consequences of commutativity for an odd centralizer complement

The three-fixed-subgroup factorization gives exponent dividing fifteen
when the complement is abelian. Consequently a cyclic complement has
order p or fifteen. An abelian complement of order twenty-seven is
actually elementary abelian, since its exponent divides both fifteen
and twenty-seven.

These discharge the elementary order/exponent steps in Bender, *Finite
groups with large subgroups* (1974), proof of (4.1), printed p.225,
citing Janko (1966), proof of Lemma 3.1. Commutativity and the order of
a noncyclic complement remain separate ambient-group obligations.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}

omit [Finite G] [IsSimpleGroup G] in
private theorem pow_fifteen_of_small_card (B : Subgroup G)
    (hc : Nat.card B = 1 ∨ Nat.card B = 3 ∨ Nat.card B = 5)
    (y : G) (hy : y ∈ B) : y ^ 15 = 1 := by
  have hd : Nat.card B ∣ 15 := by
    rcases hc with hc | hc | hc <;> rw [hc] <;> decide
  exact orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard B hy).trans hd)

/-- Once commutativity is established, the fixed-factor orders bound the exponent. -/
public theorem OddCentralizerComplement.pow_fifteen_of_commutative
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hcomm : IsMulCommutative A) (y : A) : y ^ 15 = 1 := by
  let := hcomm
  obtain ⟨t, htC, ht, htz, hti⟩ := h.exists_local_inverter p hp x hxC hx
  obtain ⟨hq, hr⟩ := a.four_fixed_orders t htC ht htz
  obtain ⟨u, v, w, hu, hv, hw, he⟩ :=
    a.four_fixed_factorization p hp hxC hx t htC ht hti y y.property
  have huA : u ∈ A := (zpowers_le.mpr a.x_mem) hu
  have hu15 : (⟨u, huA⟩ : A) ^ 15 = 1 := by
    apply Subtype.ext
    apply pow_fifteen_of_small_card (zpowers x) ?_ u hu
    rw [Nat.card_zpowers, hx]
    exact hp.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hv15 : (⟨v, hv.1⟩ : A) ^ 15 = 1 :=
    Subtype.ext (pow_fifteen_of_small_card _ hq v hv)
  have hw15 : (⟨w, hw.1⟩ : A) ^ 15 = 1 :=
    Subtype.ext (pow_fifteen_of_small_card _ hr w hw)
  have hy : y = (⟨u, huA⟩ : A) * ⟨v, hv.1⟩ * ⟨w, hw.1⟩ := Subtype.ext he
  rw [hy, mul_pow, mul_pow, hu15, hv15, hw15, one_mul, one_mul]

/-- The cyclic branch has exactly the source orders, not an assumed cardinality bound. -/
public theorem OddCentralizerComplement.card_eq_prime_or_fifteen_of_cyclic
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hcyc : IsCyclic A) : Nat.card A = p ∨ Nat.card A = 15 := by
  let := hcyc
  have hd : Nat.card A ∣ 15 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (a.pow_fifteen_of_commutative p hp hxC hx inferInstance)
  have hpd : p ∣ Nat.card A := by
    have hd := orderOf_dvd_natCard (⟨x, a.x_mem⟩ : A)
    rwa [Subgroup.orderOf_mk, hx] at hd
  have hb := Nat.le_of_dvd (by decide : 0 < 15) hd
  rcases hp with rfl | rfl
  · have arith : ∀ n : ℕ, n ≤ 15 → n ∣ 15 → 3 ∣ n → n = 3 ∨ n = 15 := by
      intro n hn hd hp
      interval_cases n <;> omega
    exact arith _ hb hd hpd
  · have arith : ∀ n : ℕ, n ≤ 15 → n ∣ 15 → 5 ∣ n → n = 5 ∨ n = 15 := by
      intro n hn hd hp
      interval_cases n <;> omega
    exact arith _ hb hd hpd

/-- In the order-27 abelian branch, the exponent restriction gives the actual elementary structure. -/
public theorem OddCentralizerComplement.elementary_of_commutative_of_card_twenty_seven
    (a : OddCentralizerComplement h x A) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p)
    (hcomm : IsMulCommutative A) (hcard : Nat.card A = 27) : IsElementaryAbelian 3 A := by
  have hexp : Monoid.exponent A ∣ 15 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (a.pow_fifteen_of_commutative p hp hxC hx hcomm)
  have hdiv : Monoid.exponent A ∣ 27 := hcard ▸ Group.exponent_dvd_nat_card
  exact { hcomm with exponent_dvd_p := by simpa using Nat.dvd_gcd hexp hdiv }

end CFSG.Quasithin.Janko1CentralizerData
