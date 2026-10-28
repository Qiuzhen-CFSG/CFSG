module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.LocalData
public import Theory.GroupTheory.PrimeOrderCentralizerSylow

/-!
# From local odd-prime counts to ambient counts

The distinguished involution centralizer has order 120, so it contains
elements of orders three and five. A centralizer of order `2p` or `30`
for one such element rules out `p²` in the group order. Thus its cyclic
subgroup is Sylow, and every element of order `p` is conjugate into the
distinguished involution centralizer. Conjugation preserves centralizers
and the literal sets of commuting and inverting involutions.

This proves the local-to-global part of Bender (4.1)–(4.2), printed
pp.225–226. The local numerical counts remain explicit inputs; their
construction and the structural order-27 exclusion are separate obligations.
-/

open Subgroup

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- Both relevant odd primes occur in the distinguished centralizer. -/
public theorem exists_prime_order_mem_centralizer
    (p : ℕ) (hp : p = 3 ∨ p = 5) :
    ∃ x : G, x ∈ centralizer ({h.z} : Set G) ∧ orderOf x = p := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ({h.z} : Set G)) p (by
      rw [h.centralizer_card]
      rcases hp with rfl | rfl <;> decide)
  exact ⟨x, x.property,
    (orderOf_injective (centralizer ({h.z} : Set G)).subtype
      Subtype.val_injective x).trans hx⟩

/-- Local centralizer orders already determine every ambient odd Sylow order. -/
public theorem sylow_card_of_local_centralizer_orders
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hC : ∀ x : G, x ∈ centralizer ({h.z} : Set G) → orderOf x = p →
      Nat.card (centralizer ({x} : Set G)) = 2 * p ∨
        Nat.card (centralizer ({x} : Set G)) = 30)
    (P : Sylow p G) : Nat.card P = p := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨x, hxC, hx⟩ := h.exists_prime_order_mem_centralizer p hp
  apply sylow_card_eq_prime_of_centralizer x hx ?_ P
  rcases hC x hxC hx with hc | hc <;>
    rcases hp with rfl | rfl <;> rw [hc] <;> norm_num

/-- The semidirect-product statement in (4.1) implies its Sylow assertion. -/
public theorem OddPrimeCentralizerStructure.sylow_card
    {h : Janko1CentralizerData G} (s : OddPrimeCentralizerStructure h)
    (p : ℕ) (hp : p = 3 ∨ p = 5) (P : Sylow p G) : Nat.card P = p :=
  h.sylow_card_of_local_centralizer_orders p hp
    (s.centralizer_card_cases p hp) P

/-- The Sylow conclusion moves every relevant element into `C_G(z)`. -/
public theorem exists_conj_mem_centralizer_of_sylow_card
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hP : ∀ P : Sylow p G, Nat.card P = p) (x : G) (hx : orderOf x = p) :
    ∃ g : G, g * x * g⁻¹ ∈ centralizer ({h.z} : Set G) := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨x₀, hx₀C, hx₀⟩ := h.exists_prime_order_mem_centralizer p hp
  exact exists_conj_mem_of_sylow_card_eq_prime _ x₀ hx₀C hx₀ hP x hx

omit [Finite G] in
private theorem centralizer_card_map (e : MulAut G) (x : G) :
    Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({e x} : Set G)) := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun y => by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    change y * x = x * y ↔ e y * e x = e x * e y
    rw [← map_mul, ← map_mul, e.injective.eq_iff])

omit [Finite G] in
private theorem commuting_count_map (e : MulAut G) (x : G) :
    Nat.card {t : G // orderOf t = 2 ∧ Commute t x} =
      Nat.card {t : G // orderOf t = 2 ∧ Commute t (e x)} := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun t => by
    change (orderOf t = 2 ∧ Commute t x) ↔
      (orderOf (e t) = 2 ∧ Commute (e t) (e x))
    rw [e.orderOf_eq]
    apply and_congr_right
    intro _
    change t * x = x * t ↔ e t * e x = e x * e t
    rw [← map_mul, ← map_mul, e.injective.eq_iff])

omit [Finite G] in
private theorem inverting_count_map (e : MulAut G) (x : G) :
    Nat.card {t : G // orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹} =
      Nat.card {t : G // orderOf t = 2 ∧ t * e x * t⁻¹ = (e x)⁻¹} := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun t => by
    change (orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹) ↔
      (orderOf (e t) = 2 ∧ e t * e x * (e t)⁻¹ = (e x)⁻¹)
    rw [e.orderOf_eq]
    apply and_congr_right
    intro _
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, e.injective.eq_iff])

/-- Local numerical statements give all eight ambient fields of
`BenderPrimeData`, including the two Sylow orders. The local source
statements themselves remain to be supplied. -/
public theorem benderPrimeData_of_local {d : ℕ} (b : LocalBenderPrimeData h d) :
    BenderPrimeData G d := by
  have h3 : ∀ P : Sylow 3 G, Nat.card P = 3 :=
    h.sylow_card_of_local_centralizer_orders 3 (Or.inl rfl) (by
      intro x hxC hx
      have hc := b.centralizer_three x hxC hx
      by_cases hd : d = 1
      · exact Or.inl (by simpa only [hd, if_true] using hc)
      · exact Or.inr (by simpa only [hd, if_false] using hc))
  have h5 : ∀ P : Sylow 5 G, Nat.card P = 5 :=
    h.sylow_card_of_local_centralizer_orders 5 (Or.inr rfl) (by
      intro x hxC hx
      have hc := b.centralizer_five x hxC hx
      rcases b.d_cases with hd | hd
      · exact Or.inl (by simpa only [hd] using hc)
      · exact Or.inr (by simpa only [hd] using hc))
  refine ⟨b.d_cases, h3, h5, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg⟩ := h.exists_conj_mem_centralizer_of_sylow_card 3 (Or.inl rfl) h3 x hx
    let e := MulAut.conj g
    rw [centralizer_card_map e x]
    exact b.centralizer_three (e x) hg ((e.orderOf_eq x).trans hx)
  · intro x hx
    obtain ⟨g, hg⟩ := h.exists_conj_mem_centralizer_of_sylow_card 5 (Or.inr rfl) h5 x hx
    let e := MulAut.conj g
    rw [centralizer_card_map e x]
    exact b.centralizer_five (e x) hg ((e.orderOf_eq x).trans hx)
  · intro x hx
    obtain ⟨g, hg⟩ := h.exists_conj_mem_centralizer_of_sylow_card 3 (Or.inl rfl) h3 x hx
    let e := MulAut.conj g
    rw [inverting_count_map e x]
    exact b.inverting_three (e x) hg ((e.orderOf_eq x).trans hx)
  · intro x hx
    obtain ⟨g, hg⟩ := h.exists_conj_mem_centralizer_of_sylow_card 3 (Or.inl rfl) h3 x hx
    let e := MulAut.conj g
    rw [commuting_count_map e x]
    exact b.commuting_three (e x) hg ((e.orderOf_eq x).trans hx)
  · intro x hx
    obtain ⟨g, hg⟩ := h.exists_conj_mem_centralizer_of_sylow_card 5 (Or.inr rfl) h5 x hx
    let e := MulAut.conj g
    rw [commuting_count_map e x]
    exact b.commuting_five (e x) hg ((e.orderOf_eq x).trans hx)

end CFSG.Quasithin.Janko1CentralizerData
