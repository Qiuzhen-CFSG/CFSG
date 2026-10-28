module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum

/-!
# Orders forced by the J₃ presentation

The first, second and fourth ATLAS relators force a nontrivial pair to
have orders 2, 3 and 19 for `x`, `y` and `x*y`, respectively. If either
generator is trivial, coprimality of the other two exponents makes both
trivial. Thus a generated nontrivial quotient has order divisible by 19.

These are word consequences in arbitrary groups. They do not construct
generators from local structure or identify a quotient with the J₃ model.
Source: ATLAS `J3G1-P1`, with the words defined in `Basic`.
-/

namespace Sporadic.Janko3.RecognitionPresentation

variable {G : Type*} [Group G] {x y : G}

private theorem eq_one_of_coprime_powers {a : G} {m n : ℕ}
    (hm : a ^ m = 1) (hn : a ^ n = 1) (hc : m.Coprime n) : a = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  simpa only [hc.gcd_eq_one] using
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)

/-- Triviality of either generator forces triviality of the other. -/
public theorem Satisfies.left_eq_one_iff (h : Satisfies x y) : x = 1 ↔ y = 1 := by
  have hx2 : x ^ 2 = 1 := h 0
  have hy3 : y ^ 3 = 1 := h 1
  have hxy19 : (x * y) ^ 19 = 1 := h 3
  constructor
  · intro hx
    rw [hx, one_mul] at hxy19
    exact eq_one_of_coprime_powers hy3 hxy19 (by decide)
  · intro hy
    rw [hy, mul_one] at hxy19
    exact eq_one_of_coprime_powers hx2 hxy19 (by decide)

/-- The literal ATLAS product has order nineteen for every nontrivial pair. -/
public theorem Satisfies.product_orderOf (h : Satisfies x y) (hx : x ≠ 1) :
    orderOf (x * y) = 19 := by
  have hx2 : x ^ 2 = 1 := h 0
  have hy3 : y ^ 3 = 1 := h 1
  have hxy19 : (x * y) ^ 19 = 1 := h 3
  have hxy : x * y ≠ 1 := by
    intro he
    have hyx : y = x⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [hyx, inv_pow, inv_eq_one] at hy3
    exact hx (eq_one_of_coprime_powers hx2 hy3 (by decide))
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact orderOf_eq_prime hxy19 hxy

/-- The first two generators have their exact prime orders. -/
public theorem Satisfies.generator_orders (h : Satisfies x y) (hx : x ≠ 1) :
    orderOf x = 2 ∧ orderOf y = 3 := by
  have hy : y ≠ 1 := fun hy => hx (h.left_eq_one_iff.mpr hy)
  exact ⟨orderOf_eq_prime (show x ^ 2 = 1 from h 0) hx,
    orderOf_eq_prime (show y ^ 3 = 1 from h 1) hy⟩

/-- A generating pair in a nontrivial quotient cannot collapse. -/
public theorem left_ne_one_of_generates [Nontrivial G]
    (h : Satisfies x y) (hgen : Subgroup.closure ({x, y} : Set G) = ⊤) : x ≠ 1 := by
  intro hx
  have hy := h.left_eq_one_iff.mp hx
  have hbot : (⊥ : Subgroup G) = ⊤ := by
    simpa only [hx, hy, Set.pair_eq_singleton, Subgroup.closure_singleton_one] using hgen
  exact bot_ne_top hbot

/-- A nontrivial generated quotient contains an element of order nineteen. -/
public theorem HasGenerators.exists_orderOf_nineteen [Nontrivial G]
    (h : HasGenerators G) : ∃ g : G, orderOf g = 19 := by
  obtain ⟨x, y, hgen, hrel⟩ := h
  exact ⟨x * y, hrel.product_orderOf (left_ne_one_of_generates hrel hgen)⟩

/-- Lagrange's consequence of the product relator, without a model comparison. -/
public theorem HasGenerators.nineteen_dvd_card [Nontrivial G]
    (h : HasGenerators G) : 19 ∣ Nat.card G := by
  obtain ⟨g, hg⟩ := h.exists_orderOf_nineteen
  exact hg ▸ orderOf_dvd_natCard g

end Sporadic.Janko3.RecognitionPresentation
