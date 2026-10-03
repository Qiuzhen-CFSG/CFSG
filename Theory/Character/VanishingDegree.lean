module
public import Theory.Character.ClassFunction
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

/-!
# Degree divisibility from vanishing on prime-singular elements

A character vanishing off the identity of a subgroup has degree divisible by
the subgroup order: averaging its restricted representation gives the dimension
of the fixed subspace, namely the degree divided by the subgroup order.
For a p-subgroup every nonidentity element has order divisible by p. Hence
vanishing on p-singular elements gives the required degree divisibility for
any p-subgroup, in particular a supplied Sylow subgroup.

Source: ordinary character orthogonality on a p-subgroup; Wong (1964),
Appendix p.106, equation (11), applies this with p = 2 and subgroup order 16.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

public theorem Representation.card_dvd_finrank_of_character_vanishes
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V)
    (hv : ∀ h : H, h ≠ 1 → ρ.character h = 0) :
    Nat.card H ∣ Module.finrank ℂ V := by
  classical
  let : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hs : ∑ h : H, ρ.character h = (Module.finrank ℂ V : ℂ) := by
    rw [Finset.sum_eq_single 1]
    · exact ρ.char_one
    · intro h _ hh
      exact hv h hh
    · simp
  have hm := ρ.card_inv_mul_sum_char_eq_finrank
  rw [hs] at hm
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have he : (Module.finrank ℂ V : ℂ) =
      (Nat.card H : ℂ) * (Module.finrank ℂ ρ.invariants : ℂ) := by
    calc
      (Module.finrank ℂ V : ℂ) = (Nat.card H : ℂ) *
          ((Nat.card H : ℂ)⁻¹ * (Module.finrank ℂ V : ℂ)) := by
        rw [mul_inv_cancel_left₀ hcard]
      _ = _ := by rw [hm]
  exact ⟨Module.finrank ℂ ρ.invariants, by exact_mod_cast he⟩

/-- Character degrees divisible by the order of a subgroup on which only the
identity has a nonzero value. -/
public theorem character_degree_dvd_of_subgroup_vanishing
    {G : Type*} [Group G] (H : Subgroup G) [Finite H]
    {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hv : ∀ h : H, h ≠ 1 → χ h = 0) :
    ∃ d : ℕ, χ 1 = (d : ℂ) ∧ Nat.card H ∣ d := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  refine ⟨n, by simp [Representation.char_one], ?_⟩
  have h := Representation.card_dvd_finrank_of_character_vanishes (ρ.comp H.subtype) hv
  simpa using h

/-- Vanishing on p-singular elements forces divisibility by the order of every
p-subgroup. This formulation retains the actual character and its degree. -/
public theorem character_degree_dvd_of_pSingular_vanishing
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [Finite H] (hH : IsPGroup p H)
    {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hv : ∀ g : G, p ∣ orderOf g → χ g = 0) :
    ∃ d : ℕ, χ 1 = (d : ℂ) ∧ Nat.card H ∣ d := by
  apply character_degree_dvd_of_subgroup_vanishing H hχ
  intro h hh
  apply hv
  rw [Subgroup.orderOf_coe]
  exact hH.dvd_orderOf hh
