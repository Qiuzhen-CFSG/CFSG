module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Localization

/-!
# Coherence of the odd-prime centralizer orders

Sylow conjugacy makes the centralizer order constant on each of the two
prime-order element families. If one centralizer has order thirty, Cauchy's
theorem supplies a commuting element of the other odd prime order. Its
centralizer is divisible by both primes, so the structural alternatives force
order thirty there too. Thus one parameter governs both families.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
p.225, the definition of `d` between (4.1) and (4.2). The structural assertion
(4.1) remains an explicit premise of this conditional result.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]


omit [Finite G] in
private theorem centralizer_card_conj (g x : G) :
    Nat.card (centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (centralizer ({x} : Set G)) := by
  let e := MulAut.conj g
  apply (Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun y =>
      y ∈ centralizer ({x} : Set G)) (q := fun y =>
      y ∈ centralizer ({e x} : Set G)) (fun y => ?_))).symm
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  change y * x = x * y ↔ e y * e x = e x * e y
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

omit [Finite G] in
private theorem centralizer_eq_of_zpowers_eq (x y : G)
    (he : zpowers x = zpowers y) :
    centralizer ({x} : Set G) = centralizer ({y} : Set G) := by
  rw [zpowers_eq_closure, zpowers_eq_closure] at he
  rw [← centralizer_closure, he, centralizer_closure]

/-- Prime-order Sylow subgroups make the centralizer order constant on
elements of that prime order, even when the elements themselves do not fuse. -/
public theorem LocalCounts.prime_centralizer_card_eq (p : ℕ) [Fact p.Prime]
    (hP : ∀ P : Sylow p G, Nat.card P = p)
    (x y : G) (hx : orderOf x = p) (hy : orderOf y = p) :
    Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_card_eq_prime (zpowers y) y
    (mem_zpowers y) hy hP x hx
  have he : zpowers (g * x * g⁻¹) = zpowers y :=
    eq_of_le_of_card_ge (zpowers_le.mpr hg) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hy]
      exact le_of_eq (((MulAut.conj g).orderOf_eq x).trans hx).symm)
  rw [← centralizer_card_conj g x, centralizer_eq_of_zpowers_eq _ _ he]

variable (h : Janko1CentralizerData G) (s : OddPrimeCentralizerStructure h)
include s

/-- Sylow conjugacy extends the structural order alternatives to all ambient
elements of the two relevant prime orders. -/
public theorem OddPrimeCentralizerStructure.ambient_card_cases (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hx : orderOf x = p) :
    Nat.card (centralizer ({x} : Set G)) = 2 * p ∨
      Nat.card (centralizer ({x} : Set G)) = 30 := by
  obtain ⟨g, hg⟩ := h.exists_conj_mem_centralizer_of_sylow_card p hp
    (s.sylow_card p hp) x hx
  have hc := s.centralizer_card_cases p hp (g * x * g⁻¹) hg
    (((MulAut.conj g).orderOf_eq x).trans hx)
  rwa [centralizer_card_conj] at hc

/-- Any two ambient elements of the same relevant prime order have
centralizers of the same cardinality. -/
public theorem OddPrimeCentralizerStructure.ambient_card_eq (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x y : G) (hx : orderOf x = p) (hy : orderOf y = p) :
    Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({y} : Set G)) := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  exact LocalCounts.prime_centralizer_card_eq p (s.sylow_card p hp) x y hx hy

private theorem other_prime_centralizer_thirty (p q : ℕ)
    (hpq : (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3))
    (x : G) (hx : orderOf x = p)
    (hc : Nat.card (centralizer ({x} : Set G)) = 30) :
    ∃ y : G, orderOf y = q ∧ Nat.card (centralizer ({y} : Set G)) = 30 := by
  have hq : q.Prime := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ({x} : Set G)) q (by
      rw [hc]
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
  have hyo : orderOf (y : G) = q :=
    (orderOf_injective (centralizer ({x} : Set G)).subtype Subtype.val_injective y).trans hy
  have hxy : x ∈ centralizer ({(y : G)} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp y.property).symm
  have hd : p ∣ Nat.card (centralizer ({(y : G)} : Set G)) := by
    have ho := orderOf_dvd_natCard (⟨x, hxy⟩ : centralizer ({(y : G)} : Set G))
    rw [← orderOf_injective (centralizer ({(y : G)} : Set G)).subtype
      Subtype.val_injective] at ho
    change orderOf x ∣ _ at ho
    rwa [hx] at ho
  refine ⟨y, hyo, ?_⟩
  rcases OddPrimeCentralizerStructure.ambient_card_cases h s q (by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp) y hyo with hsmall | hlarge
  · rw [hsmall] at hd
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at hd
  · exact hlarge

/-- The same parameter governs the ambient three- and five-centralizers. -/
public theorem exists_uniform_odd_centralizer_orders_of_structure : ∃ d : ℕ, (d = 1 ∨ d = 3) ∧
    (∀ x : G, orderOf x = 3 →
      Nat.card (centralizer ({x} : Set G)) = if d = 1 then 6 else 30) ∧
    (∀ x : G, orderOf x = 5 → Nat.card (centralizer ({x} : Set G)) = 10 * d) := by
  obtain ⟨x, _, hx⟩ := h.exists_prime_order_mem_centralizer 3 (Or.inl rfl)
  rcases OddPrimeCentralizerStructure.ambient_card_cases h s 3 (Or.inl rfl) x hx with hc | hc
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · intro y hy
      exact (OddPrimeCentralizerStructure.ambient_card_eq h s 3 (Or.inl rfl) y x hy hx).trans hc
    · intro y hy
      rcases OddPrimeCentralizerStructure.ambient_card_cases h s 5 (Or.inr rfl) y hy with hsmall | hlarge
      · exact hsmall
      · obtain ⟨v, hv, hvC⟩ := other_prime_centralizer_thirty h s 5 3
          (Or.inr ⟨rfl, rfl⟩) y hy hlarge
        have he := OddPrimeCentralizerStructure.ambient_card_eq h s 3 (Or.inl rfl) x v hx hv
        rw [hc, hvC] at he
        contradiction
  · obtain ⟨y, hy, hyC⟩ := other_prime_centralizer_thirty h s 3 5
      (Or.inl ⟨rfl, rfl⟩) x hx hc
    refine ⟨3, Or.inr rfl, ?_, ?_⟩
    · intro v hv
      exact (OddPrimeCentralizerStructure.ambient_card_eq h s 3 (Or.inl rfl) v x hv hx).trans hc
    · intro v hv
      exact (OddPrimeCentralizerStructure.ambient_card_eq h s 5 (Or.inr rfl) v y hv hy).trans hyC

end CFSG.Quasithin.Janko1CentralizerData
