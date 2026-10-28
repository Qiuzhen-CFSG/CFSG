module

public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# Cubic subgroups fixing a vector on paired natural planes

A nonzero common fixed vector has a nonzero coordinate. If all nonidentity
coordinate actors have order three, the fixed-point calculation for the natural
SL₂ plane forces the subgroup into the kernel of that coordinate action.
The assertion uses actual matrix actions and does not assume that the subgroup
is already contained in an axis.

Source: the torus-alignment step in Aschbacher–Smith10.2.3(4), printed p.746.
-/

public section

open Matrix
open scoped MatrixGroups
namespace Representation.SL2.PairedCubicAxes

variable {F H : Type*} [Field F] [CharP F 2] [Group H]

/-- A cubic coordinate subgroup with a nonzero common fixed vector lies in one
coordinate kernel. No restriction on the other coordinate of that vector is
needed. -/
theorem le_kernel_or_le_kernel_of_nonzero_fixed
    (q₁ q₂ : H →* SL(2,F)) (P : Subgroup H)
    (h₁ : ∀ p ∈ P, q₁ p = 1 ∨ orderOf (q₁ p) = 3)
    (h₂ : ∀ p ∈ P, q₂ p = 1 ∨ orderOf (q₂ p) = 3)
    (v : (Fin 2 → F) × (Fin 2 → F)) (hv : v ≠ 0)
    (hfix : ∀ p ∈ P, ((q₁ p).val *ᵥ v.1, (q₂ p).val *ᵥ v.2) = v) :
    P ≤ q₁.ker ∨ P ≤ q₂.ker := by
  classical
  by_cases hv₁ : v.1 = 0
  · right
    have hv₂ : v.2 ≠ 0 := by
      intro hz
      exact hv (Prod.ext hv₁ hz)
    intro p hp
    change q₂ p = 1
    rcases h₂ p hp with he | ho
    · exact he
    · exact False.elim (hv₂ (Matrix.SL2.cubic_fixed_eq_zero (q₂ p) ho v.2
        (congrArg Prod.snd (hfix p hp))))
  · left
    intro p hp
    change q₁ p = 1
    rcases h₁ p hp with he | ho
    · exact he
    · exact False.elim (hv₁ (Matrix.SL2.cubic_fixed_eq_zero (q₁ p) ho v.1
        (congrArg Prod.fst (hfix p hp))))

/-- The common fixed-vector criterion for a subgroup of exponent dividing
three, with no separate assumption on either coordinate image. -/
theorem le_kernel_or_le_kernel_of_cube_eq_one
    (q₁ q₂ : H →* SL(2,F)) (P : Subgroup H)
    (hP : ∀ p ∈ P, p ^ 3 = 1)
    (v : (Fin 2 → F) × (Fin 2 → F)) (hv : v ≠ 0)
    (hfix : ∀ p ∈ P, ((q₁ p).val *ᵥ v.1, (q₂ p).val *ᵥ v.2) = v) :
    P ≤ q₁.ker ∨ P ≤ q₂.ker := by
  have hc (q : H →* SL(2,F)) (p : H) (hp : p ∈ P) :
      q p = 1 ∨ orderOf (q p) = 3 := by
    by_cases he : q p = 1
    · exact Or.inl he
    · exact Or.inr (orderOf_eq_prime (by rw [← map_pow, hP p hp, map_one]) he)
  exact le_kernel_or_le_kernel_of_nonzero_fixed q₁ q₂ P (hc q₁) (hc q₂) v hv hfix

end Representation.SL2.PairedCubicAxes
