module

public import Theory.Character.PrimeOrderRationalValues
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.Linarith

/-!
# The rational degree-27 value on a self-centralizing seven subgroup

Rational values are integral and congruent to the degree modulo seven.
Column orthogonality bounds their squares by seven, forcing value minus one.
No block membership or automizer hypothesis is needed.

Source: Fong (1967), printed p.75. Adapted from `CyclicThirteenBlock`.
-/

noncomputable section
namespace CyclicSevenBlock
variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_eq_of_prime_card {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : Nat.card P = p)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (u : P) (hu : u ≠ 1) : Subgroup.centralizer ({(u : G)} : Set G) = P := by
  have hpw : u ^ p = 1 := by simpa only [hP] using (pow_card_eq_one' (x := u))
  have ho : orderOf (u : G) = p := by
    exact (Subgroup.orderOf_coe u).trans (orderOf_eq_prime hpw hu)
  have hz : Subgroup.zpowers (u : G) = P :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.property)
      (by rw [Nat.card_zpowers, ho]; exact hP.le)
  calc
    Subgroup.centralizer ({(u : G)} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    _ = Subgroup.centralizer (P : Set G) := by rw [hz]
    _ = P := hC

private theorem value_data {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) {n : ℕ}
    (hd : χ (ConjClasses.mk 1) = (n : ℂ))
    (P : Sylow 7 G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (u : P) (hu : u ≠ 1)
    (hrat : ∃ q : ℚ, χ (ConjClasses.mk (u : G)) = (q : ℂ)) :
    ∃ z : ℤ, χ (ConjClasses.mk (u : G)) = (z : ℂ) ∧
      7 ∣ z - n ∧ -3 ≤ z ∧ z ≤ 3 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hcard : Nat.card ↥P = 7 := hP
  have hpw : u ^ 7 = 1 := by simpa only [hcard] using (pow_card_eq_one' (x := u))
  have hpwG : (u : G) ^ 7 = 1 := by exact_mod_cast hpw
  obtain ⟨z, hz, hmod, hbound⟩ :=
    PrimeOrderRationalValues.integer_value_congruence_bound hχ (by decide) hd (u : G) hpwG hrat
  rw [centralizer_eq_of_prime_card (P : Subgroup G) hP hC u hu,
    hP] at hbound
  norm_num at hbound
  have hb : -4 < z ∧ z < 4 := by
    constructor <;> nlinarith [sq_nonneg (z + 4), sq_nonneg (z - 4)]
  exact ⟨z, hz, hmod, by omega, by omega⟩

/-- The rational degree-27 row takes value minus one on nonidentity elements of
a self-centralizing Sylow subgroup of order 7. -/
public theorem degree_twenty_seven_value {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ)
    (hd : χ (ConjClasses.mk 1) = 27)
    (P : Sylow 7 G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (u : P) (hu : u ≠ 1)
    (hrat : ∃ q : ℚ, χ (ConjClasses.mk (u : G)) = (q : ℂ)) :
    χ (ConjClasses.mk (u : G)) = -1 := by
  obtain ⟨z, hz, hmod, hlo, hhi⟩ := value_data hχ (n := 27) hd P hP hC u hu hrat
  have hz1 : z = -1 := by omega
  simpa [hz1] using hz


end CyclicSevenBlock
