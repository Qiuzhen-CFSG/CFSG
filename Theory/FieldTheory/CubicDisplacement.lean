module
public import Theory.FieldTheory.UnitInversion
public import Mathlib.Tactic.FinCases
/-!
# Cubic displacement of characteristic-two field automorphisms

If an automorphism fixes all cubes, expansion at x + 1 shows that it sends
x to x or x + 1. A moved element then restricts the fixed field to {0,1}
and the entire field to four elements. Equivalently, an automorphism whose
unit displacements have cube one is trivial unless the field has at most
four elements.

This is the field calculation used on the literal Borel quotients in
Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
-/

public section
namespace FiniteField
variable {F : Type*} [Field F] [CharP F 2]
theorem eq_one_or_card_le_four_of_cubes_fixed (σ : F ≃+* F)
    (hσ : ∀ x : F, σ (x ^ 3) = x ^ 3) : σ = 1 ∨ Nat.card F ≤ 4 := by
  classical
  by_cases he : σ = 1
  · exact Or.inl he
  right
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc (x : F) : (σ x) ^ 3 = x ^ 3 := by rw [←map_pow,hσ]
  have hd (x : F) : σ x = x ∨ σ x = x+1 := by
    have h0 : (σ x-x) * (σ x-x-1) = 0 := by
      have h := hc (x+1)
      rw [map_add,map_one] at h
      linear_combination h - hc x +
        (-2*σ x-σ x*x-(σ x)^2+2*x+2*x^2)*h2
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
  obtain ⟨a,ha⟩ : ∃ a : F, σ a ≠ a := by
    by_contra! h
    exact he (RingEquiv.ext h)
  have hsa := (hd a).resolve_left ha
  have hfix (x : F) (hx : σ x = x) : x = 0 ∨ x = 1 := by
    rcases hd (a*x) with h | h
    · rw [map_mul,hsa,hx] at h
      exact Or.inl (by linear_combination h)
    · rw [map_mul,hsa,hx] at h
      exact Or.inr (by linear_combination h)
  have hall (x : F) : x = 0 ∨ x = 1 ∨ x = a ∨ x = a+1 := by
    rcases hd x with hx | hx
    · rcases hfix x hx with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hxa : σ (x+a) = x+a := by
        rw [map_add,hx,hsa]
        linear_combination h2
      rcases hfix (x+a) hxa with h|h
      · exact Or.inr (Or.inr (Or.inl (by
          simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h)))
      · exact Or.inr (Or.inr (Or.inr (by
          have heq : x = 1-a := eq_sub_of_add_eq h
          simpa only [sub_eq_add_neg,CharTwo.neg_eq,add_comm] using heq)))
  let f : Fin 4 → F := ![0,1,a,a+1]
  have hf : Function.Surjective f := by
    intro x
    rcases hall x with rfl|rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf

/-- The unit displacement criterion, with the given field automorphism. -/
theorem eq_one_or_card_le_four_of_unit_displacement_cube (σ : F ≃+* F)
    (hσ : ∀ u : Fˣ, (Units.map σ.toMonoidHom u * u⁻¹)^3 = 1) :
    σ = 1 ∨ Nat.card F ≤ 4 := by
  apply eq_one_or_card_le_four_of_cubes_fixed σ
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have h := hσ (Units.mk0 x hx)
  have he : (Units.map σ.toMonoidHom (Units.mk0 x hx))^3 = (Units.mk0 x hx)^3 := by
    have hh := h
    rw [mul_pow,inv_pow,mul_inv_eq_one] at hh
    exact hh
  have hh := congrArg Units.val he
  change (σ x)^3 = x^3 at hh
  rwa [map_pow]
end FiniteField
