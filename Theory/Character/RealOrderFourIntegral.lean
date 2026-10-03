module

public import Theory.Character.ClassFunction
public import Theory.Character.Peterfalvi1.Basic
public import Theory.Representation.Induction
public import Mathlib.Tactic.Ring

/-!
# Integral character values at real elements of order dividing four

Fusion of an element with its inverse makes each ordinary character value
real. Each eigenvalue is a fourth root of unity, whose real part is an integer;
the trace therefore has integral real part and vanishing imaginary part.

Source: the usual rational order-four character argument, used by Lyons,
*A Characterization of the Group U₃(4)* (1972), p. 373, equation (3.1).
The fourth-root calculation also occurs in `ModularBlock.TwistedBrauerExpansion`.
-/

public section
noncomputable section
open scoped BigOperators
private theorem re_int_of_fourth_root {c : ℂ} (hc : c ^ 4 = 1) : ∃ k : ℤ, c.re = (k : ℝ) := by
  have hs : (c ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hc
  rcases sq_eq_one_iff.mp hs with hs | hs
  · rcases sq_eq_one_iff.mp hs with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  · have hprod : (c - Complex.I) * (c + Complex.I) = 0 := by
      calc
        _ = c ^ 2 + 1 := by ring_nf; simp [add_comm]
        _ = 0 := by rw [hs]; ring
    rcases mul_eq_zero.mp hprod with h | h
    · have : c = Complex.I := sub_eq_zero.mp h
      exact ⟨0, by simp [this]⟩
    · have : c = -Complex.I := eq_neg_of_add_eq_zero_left h
      exact ⟨0, by simp [this]⟩

/-- A real element whose fourth power is one has integral ordinary character values. -/
theorem IsCharacter.exists_int_of_fourth_power_of_isConj_inv
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G} (hχ : IsCharacter χ)
    (g : G) (hg : g ^ 4 = 1) (hi : IsConj g g⁻¹) : ∃ k : ℤ, χ g = (k : ℂ) := by
  classical
  obtain ⟨n, ρ, rfl⟩ := hχ
  let f : Module.End ℂ (Fin n → ℂ) := ρ g
  have hpow : (ρ g) ^ 4 = 1 := by rw [← map_pow, hg, map_one]
  have he := Representation.trace_pow_eq_sum_eigenvalues (f := ρ g) (n := 4) (k := 1)
    (by decide) hpow
  have he' : ρ.character g = ∑ μ : f.Eigenvalues,
      (μ : ℂ) * (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℂ) := by
    simpa [Representation.character] using he
  choose k hk using fun μ : f.Eigenvalues => re_int_of_fourth_root (c := (μ : ℂ))
    (Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property)
  let z : ℤ := ∑ μ : f.Eigenvalues, k μ * (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℤ)
  have hre : (ρ.character g).re = (z : ℝ) := by
    dsimp only [z]
    rw [he']
    simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      mul_zero, sub_zero, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro μ _
    rw [hk μ]
  have hc : star (ρ.character g) = ρ.character g := by
    rw [← Representation.representation_character_inv_eq_star_character]
    obtain ⟨x, hx⟩ := isConj_iff.mp hi
    rw [← hx]
    exact ρ.char_conj g x
  refine ⟨z, ?_⟩
  apply Complex.ext
  · simpa only [Complex.intCast_re] using hre
  · have him := congrArg Complex.im hc
    simpa using (show (ρ.character g).im = 0 by simpa using (neg_eq_self.mp him))
