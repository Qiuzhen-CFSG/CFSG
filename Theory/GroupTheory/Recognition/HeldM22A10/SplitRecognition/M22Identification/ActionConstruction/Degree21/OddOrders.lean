module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.OddOrders.ThreeCentralizer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.OddOrders.PrimeCentralizers

/-!
# Janko's odd element orders from the original local inputs

The elementary Sylow three-groups exclude order nine. The order-72
three-normalizers sharpen the order-three centralizer to order 36. Sylow
normalizer actions and the subgroup of order 21 give centralizer orders seven
and eleven at those primes. An element whose order is divisible by a prime
centralizes its prime-order power, so its order divides the corresponding
centralizer order. The ambient order and parity then leave exactly the odd
orders 1, 3, 5, 7, 11.

`odd_orders` uses only the original local analysis, ambient order and
three-normalizer order, together with finiteness and simplicity. The separate
`OddOrders.CharacterApplication` extension applies this result to the existing
degree-21 assembly. Keeping that application separate lets the degree-21
construction import this spectrum without an import cycle.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 2–7, especially the order/value table on p.16,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy CaseII
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem order_dvd_of_prime_centralizer
    {p c : ℕ} (hC : ∀ x : G, orderOf x = p → Nat.card (centralizer ({x} : Set G)) = c)
    (g : G) (hp : p ∣ orderOf g) : orderOf g ∣ c := by
  let x := g ^ (orderOf g / p)
  have hx : orderOf x = p := orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos g)) hp
  have hg : g ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr ((Commute.refl g).pow_right _).eq
  exact hC x hx ▸ Subgroup.orderOf_dvd_natCard _ hg

/-- The complete odd spectrum, including exclusion of mixed orders and order nine. -/
public theorem odd_orders [IsSimpleGroup G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (g : G) (hg : Odd (orderOf g)) : orderOf g ∈ ({1, 3, 5, 7, 11} : Finset ℕ) := by
  have h3 := OddOrders.three_centralizer_card D k L hN3
  have h9 := OddOrders.not_nine_dvd_order D k L g
  by_cases hd3 : 3 ∣ orderOf g
  · have hd := order_dvd_of_prime_centralizer h3 g hd3
    have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 36 = {1, 2, 3, 4, 6, 9, 12, 18, 36} by decide] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
      simp_all [Nat.odd_iff]
  by_cases hd7 : 7 ∣ orderOf g
  · have hd := order_dvd_of_prime_centralizer
      (OddOrders.seven_centralizer_card D k L hcard h3) g hd7
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with h | h <;> simp [h]
  by_cases hd11 : 11 ∣ orderOf g
  · have hd := order_dvd_of_prime_centralizer
      (OddOrders.eleven_centralizer_card D k L hcard h3) g hd11
    rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp hd with h | h <;> simp [h]
  have hc2 : (orderOf g).Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by simpa only [← even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hg))).symm
  have hc3 : (orderOf g).Coprime 3 :=
    ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hd3).symm
  have hc7 : (orderOf g).Coprime 7 :=
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr hd7).symm
  have hc11 : (orderOf g).Coprime 11 :=
    ((by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr hd11).symm
  have hcop : (orderOf g).Coprime 88704 := by
    rw [show 88704 = (2 ^ 7 * 3 ^ 2) * 7 * 11 by decide]
    simp only [Nat.coprime_mul_iff_right]
    exact ⟨⟨⟨hc2.pow_right 7, hc3.pow_right 2⟩, hc7⟩, hc11⟩
  have hd : orderOf g ∣ 5 :=
    hcop.dvd_of_dvd_mul_left (show orderOf g ∣ 88704 * 5 by simpa [hcard] using orderOf_dvd_natCard g)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h <;> simp [h]


end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
