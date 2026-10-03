module

public import Theory.Character.ClassFunction
public import Theory.Character.Integrality
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Tactic

/-!+# Ordinary character projectors and defect-zero denominators

The normalized ordinary character projector has coefficient
`χ(1) χ(g⁻¹) / |G|` at `g`. If the order of a Sylow `p`-subgroup divides
the character degree, multiplying every coefficient by the Sylow index
makes it an algebraic integer. The index is prime to `p`, so these are
precisely the coefficient denominators permitted in a `p`-local argument.

This module proves the coefficient calculation without any block-membership
or field-of-realization hypothesis. Idempotence for an irreducible character
and the support theorem for integral local idempotents are separate steps.

Source: the ordinary central-idempotent proof of defect-zero vanishing,
as used by Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)* (1967), pp. 74–75.
-/

public section
noncomputable section

namespace OrdinaryCharacter

attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

/-- The normalized group-algebra element associated with an ordinary character.
For an irreducible character it is the primitive central projector. -/
noncomputable def projector (χ : ClassFunction G) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff
    ((Finsupp.equivFunOnFinite : (G →₀ ℂ) ≃ (G → ℂ)).symm
      (fun g => χ 1 / (Nat.card G : ℂ) * χ g⁻¹))

@[simp] theorem projector_coeff (χ : ClassFunction G) (g : G) :
    (projector χ).coeff g = χ 1 / (Nat.card G : ℂ) * χ g⁻¹ := by
  classical
  simp [projector]

/-- Conjugacy invariance alone makes the normalized projector central. -/
theorem projector_mem_center {χ : ClassFunction G} (hχ : IsClassFunction χ) :
    projector χ ∈ Set.center (MonoidAlgebra ℂ G) := by
  classical
  rw [Semigroup.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single g r =>
    ext x
    rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply]
    have hconj : χ (g⁻¹ * x)⁻¹ = χ (x * g⁻¹)⁻¹ := by
      simpa [mul_assoc] using hχ (g * x⁻¹) g⁻¹
    simp only [projector_coeff]
    rw [hconj]
    ring

/-- An ordinary character has integral values. -/
theorem value_isIntegral {χ : ClassFunction G} (hχ : IsCharacter χ) (g : G) :
    IsIntegral ℤ (χ g) := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  exact character_value_isIntegral ρ g

/-- The Sylow index clears the normalized projector's denominators when the
Sylow order divides the degree. This does not require irreducibility. -/
theorem index_mul_projector_coeff_isIntegral {p n : ℕ} [Fact p.Prime]
    (P : Sylow p G) {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hdegree : χ 1 = (n : ℂ)) (hdiv : Nat.card P ∣ n) (g : G) :
    IsIntegral ℤ ((P.index : ℂ) * (projector χ).coeff g) := by
  obtain ⟨k, rfl⟩ := hdiv
  have hcard : (Nat.card G : ℂ) = (Nat.card P : ℂ) * (P.index : ℂ) := by
    exact_mod_cast (P : Subgroup G).card_mul_index.symm
  have hP : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hindex : (P.index : ℂ) ≠ 0 := by
    intro h
    have : (Nat.card G : ℂ) = 0 := by rw [hcard, h, mul_zero]
    exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') this
  have heq : (P.index : ℂ) * (projector χ).coeff g = (k : ℂ) * χ g⁻¹ := by
    rw [projector_coeff, hdegree, Nat.cast_mul, hcard]
    field_simp
  rw [heq]
  have hk : IsIntegral ℤ (k : ℂ) := isIntegral_algebraMap
  exact hk.mul (value_isIntegral hχ g⁻¹)

/-- Defect-zero projector coefficients are algebraic integers with denominators
prime to `p`. The single denominator `P.index` works for every coefficient. -/
theorem projector_coeff_integralAway {p n : ℕ} [Fact p.Prime]
    (P : Sylow p G) {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hdegree : χ 1 = (n : ℂ)) (hdiv : Nat.card P ∣ n) :
    ∃ m : ℕ, ¬ p ∣ m ∧
      ∀ g : G, IsIntegral ℤ ((m : ℂ) * (projector χ).coeff g) :=
  ⟨P.index, P.not_dvd_index,
    index_mul_projector_coeff_isIntegral P hχ hdegree hdiv⟩

/-- A zero inverse coefficient of the normalized projector is a zero character
value, provided that the character degree is nonzero. -/
theorem value_eq_zero_of_projector_coeff_inv_eq_zero {χ : ClassFunction G}
    (hdegree : χ 1 ≠ 0) (g : G) (hg : (projector χ).coeff g⁻¹ = 0) :
    χ g = 0 := by
  simpa only [projector_coeff, inv_inv,
    mul_eq_zero, div_eq_zero_iff, or_iff_right hdegree,
    or_iff_right (Nat.cast_ne_zero.mpr Nat.card_pos.ne')] using hg

end OrdinaryCharacter
