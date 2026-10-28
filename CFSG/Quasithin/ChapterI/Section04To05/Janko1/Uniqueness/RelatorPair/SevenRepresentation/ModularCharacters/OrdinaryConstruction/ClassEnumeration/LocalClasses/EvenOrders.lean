module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.LocalClasses.PrimeClasses
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.TwoPart

/-!
# The actual classes of orders six and ten in the J₁ source group

Choose a commuting involution for each of the previously constructed
prime-order representatives. For orders three and five their products have
orders six and ten. The `(p + 1)`st and `p`th powers recover the prime-order
factor and the involution, respectively. Thus the product centralizer is the
intersection of the two factor centralizers, and conjugate products have
conjugate prime-order factors.

The supplied involution fusion transports each common centralizer to one
inside the distinguished involution centralizer. Its actual `A₅ × C₂`
structure gives order `2p`. This constructs one order-six class and two
pairwise nonconjugate order-ten classes, with full ambient centralizers.
The existing class-size assembly is responsible for exhaustiveness.

Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*,
§16.6, printed p.482. See `../../Source.md` for the source conventions.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
variable {G : Type*} [Group G]

private theorem product_powers (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x t : G) (hx : orderOf x = p) (ht : orderOf t = 2) (hxt : Commute x t) :
    (x * t) ^ (p + 1) = x ∧ (x * t) ^ p = t := by
  constructor
  · rw [hxt.mul_pow, ← pow_mod_orderOf x (p + 1), ← pow_mod_orderOf t (p + 1), hx, ht]
    rcases hp with rfl | rfl <;> simp
  · rw [hxt.mul_pow, ← pow_mod_orderOf x p, ← pow_mod_orderOf t p, hx, ht]
    rcases hp with rfl | rfl <;> simp

private theorem product_centralizer (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x t : G) (hx : orderOf x = p) (ht : orderOf t = 2) (hxt : Commute x t) :
    centralizer ({x * t} : Set G) =
      centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) := by
  obtain ⟨hpx, hpt⟩ := product_powers p hp x t hx ht hxt
  ext y
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    have hc : Commute y (x * t) := hy
    exact ⟨by simpa only [hpt] using (hc.pow_right p).eq,
      by simpa only [hpx] using (hc.pow_right (p + 1)).eq⟩
  · rintro ⟨hyt, hyx⟩
    exact (show Commute y x from hyx).mul_right (show Commute y t from hyt)

variable [Finite G]

private theorem common_centralizer_card (h : Janko1CentralizerData G)
    (hfusion : ∀ t : G, orderOf t = 2 → ∃ g : G, g * t * g⁻¹ = h.z)
    (p : ℕ) (hp : p = 3 ∨ p = 5) (x t : G)
    (hx : orderOf x = p) (ht : orderOf t = 2) (hxt : Commute x t) :
    Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) =
      2 * p := by
  obtain ⟨g, hg⟩ := hfusion t ht
  let e := MulAut.conj g
  have het : e t = h.z := hg
  have hext : e x ∈ centralizer ({h.z} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← het, ← map_mul, ← map_mul, hxt.eq]
  have hecard : Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) =
      Nat.card (centralizer ({e t} : Set G) ⊓ centralizer ({e x} : Set G) : Subgroup G) := by
    apply Nat.card_congr
    exact e.toEquiv.subtypeEquiv (fun y => by
      simp only [mem_inf, mem_centralizer_singleton_iff]
      change (y * t = t * y ∧ y * x = x * y) ↔
        (e y * e t = e t * e y ∧ e y * e x = e x * e y)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
        e.injective.eq_iff, e.injective.eq_iff])
  rw [hecard, het]
  exact h.odd_prime_common_centralizer_card p hp (e x) hext ((e.orderOf_eq x).trans hx)

private theorem even_block_of_prime_block (h : Janko1CentralizerData G)
    (hfusion : ∀ t : G, orderOf t = 2 → ∃ g : G, g * t * g⁻¹ = h.z)
    (p : ℕ) (hp : p = 3 ∨ p = 5) {c k : ℕ} (b : ClassBlock G p c k)
    (hex : ∀ x : G, orderOf x = p → ∃ t : G, orderOf t = 2 ∧ Commute t x) :
    Nonempty (ClassBlock G (2 * p) (2 * p) k) := by
  choose t ht hc using fun i => hex (b.representatives i) (b.orders i)
  refine ⟨⟨fun i => b.representatives i * t i, ?_, ?_, ?_⟩⟩
  · intro i
    rw [(hc i).symm.orderOf_mul_eq_mul_orderOf_of_coprime, b.orders i, ht i]
    · exact Nat.mul_comm _ _
    · rw [b.orders i, ht i]
      rcases hp with rfl | rfl <;> decide
  · intro i
    rw [product_centralizer p hp _ _ (b.orders i) (ht i) (hc i).symm]
    exact common_centralizer_card h hfusion p hp _ _ (b.orders i) (ht i) (hc i).symm
  · intro i j hij
    apply b.distinct
    have hpij := (ConjClasses.mk_eq_mk_iff_isConj.mp hij).pow (p + 1)
    rw [(product_powers p hp _ _ (b.orders i) (ht i) (hc i).symm).1,
      (product_powers p hp _ _ (b.orders j) (ht j) (hc j).symm).1] at hpij
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hpij

variable [IsSimpleGroup G]

/-- Construct an actual order-six representative with ambient centralizer order six. -/
public theorem six_classes_nonempty (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560)
    (hfusion : ∀ t : G, orderOf t = 2 → ∃ g : G, g * t * g⁻¹ = h.z) :
    Nonempty (ClassBlock G 6 6 1) := by
  obtain ⟨b⟩ := three_classes_nonempty h horder
  apply even_block_of_prime_block h hfusion 3 (Or.inl rfl) b
  intro x hx
  have hc := (benderPrimeData_of_order h horder).commuting_three x hx
  have hn : Nonempty {t : G // orderOf t = 2 ∧ Commute t x} :=
    (Nat.card_pos_iff.mp (by omega : 0 < Nat.card {t : G // orderOf t = 2 ∧ Commute t x})).1
  obtain ⟨t⟩ := hn
  exact ⟨t.val, t.property⟩

/-- Construct two nonconjugate order-ten representatives, each with ambient
centralizer order ten. -/
public theorem ten_classes_nonempty (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560)
    (hfusion : ∀ t : G, orderOf t = 2 → ∃ g : G, g * t * g⁻¹ = h.z) :
    Nonempty (ClassBlock G 10 10 2) := by
  obtain ⟨b⟩ := five_classes_nonempty h horder
  apply even_block_of_prime_block h hfusion 5 (Or.inr rfl) b
  intro x hx
  have hc := (benderPrimeData_of_order h horder).commuting_five x hx
  have hn : Nonempty {t : G // orderOf t = 2 ∧ Commute t x} :=
    (Nat.card_pos_iff.mp (by omega : 0 < Nat.card {t : G // orderOf t = 2 ∧ Commute t x})).1
  obtain ⟨t⟩ := hn
  exact ⟨t.val, t.property⟩
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
