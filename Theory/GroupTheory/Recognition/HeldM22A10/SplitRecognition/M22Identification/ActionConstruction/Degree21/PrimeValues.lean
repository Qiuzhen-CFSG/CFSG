module

public import Mathlib.GroupTheory.Sylow
public import Theory.Character.PrimePowerIntegralCongruence
public import Theory.Character.ColumnBound
public import Theory.Character.DefectZeroVanishing

/-!
# The prime-order values in Janko's degree-21 row

Once the order spectrum is known, an element centralizing an element of
order five or eleven has order one or that same prime: a commuting element
of any other allowed order would produce a forbidden product order. Its
centralizer is therefore a p-group. The ambient order has p-part p, forcing
the centralizer to have order p.

For an integer-valued irreducible character of degree 21, column orthogonality
and the prime-order trace congruence then force the values 1 and -1 at orders
five and eleven. The value at order seven is zero by ordinary defect-zero
vanishing. These are conditional value calculations, not the construction
or uniqueness of an irreducible character.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.15--16,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem character_of_irreducible {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : IsCharacter χ := by
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  exact ⟨n, ρ, rfl⟩

/-- The order spectrum forces prime centralizers at orders five and eleven. -/
public theorem prime_centralizer_card_of_orders
    (hcard : Nat.card G = 443520)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ))
    {p : ℕ} (hp : p = 5 ∨ p = 11) (g : G) (hg : orderOf g = p) :
    Nat.card (centralizer ({g} : Set G)) = p := by
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  have hnum (n : ℕ) (hn : n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ)) :
      n = 1 ∨ n = p ∨ (n.Coprime p ∧ n * p ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ)) := by
    rcases hp with rfl | rfl <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn <;>
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have ho (x : centralizer ({g} : Set G)) : orderOf x = 1 ∨ orderOf x = p := by
    rcases hnum (orderOf (x : G)) (horders x) with h | h | ⟨hcop, hnot⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
    · have hc : Commute (x : G) g := mem_centralizer_singleton_iff.mp x.property
      have he := hc.orderOf_mul_eq_mul_orderOf_of_coprime (by simpa [hg] using hcop)
      have hh := horders ((x : G) * g)
      rw [he, hg] at hh
      exact False.elim (hnot hh)
  have hC : IsPGroup p (centralizer ({g} : Set G)) := by
    apply IsPGroup.iff_orderOf.mpr
    intro x
    rcases ho x with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨P, hP⟩ := hC.exists_le_sylow
  have hPcard : Nat.card P = p := by
    rw [P.card_eq_multiplicity, hcard]
    rcases hp with rfl | rfl <;> decide +kernel
  apply Nat.dvd_antisymm
  · simpa [hPcard] using card_dvd_of_le hP
  · rw [← hg]
    exact Subgroup.orderOf_dvd_natCard _ (mem_centralizer_singleton_iff.mpr rfl)

/-- Integrality, the prime congruence, and the column bound force value 1
at a self-centralizing element of order five. -/
public theorem value_at_five {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hd : χ 1 = 21)
    (hi : ∀ g, ∃ a : ℤ, χ g = (a : ℂ)) (g : G) (hg : orderOf g = 5)
    (hc : Nat.card (centralizer ({g} : Set G)) = 5) : χ g = 1 := by
  obtain ⟨a, ha⟩ := hi g
  have hp : g ^ (5 ^ 1) = 1 := by simpa [hg] using pow_orderOf_eq_one g
  have hmod := (character_of_irreducible hχ).prime_dvd_degree_sub_integer_value
    g (by decide : Nat.Prime 5) hp 21 a (by simpa using hd) ha
  have hb := hχ.normSq_le_centralizer_card g
  rw [ha, hc] at hb
  have hb' : (a : ℝ) ^ 2 ≤ 5 := by
    simpa [Complex.normSq_apply, pow_two] using hb
  have hbZ : a ^ 2 ≤ 5 := by exact_mod_cast hb'
  have hlow : -2 ≤ a := by nlinarith
  have hhigh : a ≤ 2 := by nlinarith
  have he : a = 1 := by omega
  simpa [he] using ha

/-- The analogous order-eleven calculation forces value -1. -/
public theorem value_at_eleven {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hd : χ 1 = 21)
    (hi : ∀ g, ∃ a : ℤ, χ g = (a : ℂ)) (g : G) (hg : orderOf g = 11)
    (hc : Nat.card (centralizer ({g} : Set G)) = 11) : χ g = -1 := by
  obtain ⟨a, ha⟩ := hi g
  have hp : g ^ (11 ^ 1) = 1 := by simpa [hg] using pow_orderOf_eq_one g
  have hmod := (character_of_irreducible hχ).prime_dvd_degree_sub_integer_value
    g (by decide : Nat.Prime 11) hp 21 a (by simpa using hd) ha
  have hb := hχ.normSq_le_centralizer_card g
  rw [ha, hc] at hb
  have hb' : (a : ℝ) ^ 2 ≤ 11 := by
    simpa [Complex.normSq_apply, pow_two] using hb
  have hbZ : a ^ 2 ≤ 11 := by exact_mod_cast hb'
  have hlow : -3 ≤ a := by nlinarith
  have hhigh : a ≤ 3 := by nlinarith
  have he : a = -1 := by omega
  simpa [he] using ha

/-- Degree 21 has defect zero at seven since the ambient Sylow seven-group
has order seven. This forces vanishing without any rationality premise. -/
public theorem value_at_seven {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hd : χ 1 = 21)
    (hcard : Nat.card G = 443520) (g : G) (hg : orderOf g = 7) : χ g = 0 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 G := Classical.choice inferInstance
  have hP : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, hcard]
    decide +kernel
  exact OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree P hχ hd
    (by rw [hP]; decide) g (by rw [hg])

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
