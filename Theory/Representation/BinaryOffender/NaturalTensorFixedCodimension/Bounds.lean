module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Realization
import Mathlib.Tactic

/-!
# Numerical bounds for natural sums and genuine tensor modules

Equivariant binary coordinates reduce the actual SL₂ action to the amplified
natural representation. Arbitrary inner and inner-field intertwiners are allowed,
including operators mixing or permuting natural summands. On the genuine tensor
product over F the multiplicity space is F², giving the bound 2n over F₂.

Source: GLS, vol. 2, Theorem 26.24, final paragraph, ChapterG.tex, lines 1240–1248.
Existence of the equivariant realization is an explicit local input, supplied
by the quadratic four-group theorem in the source application.
-/
@[expose] public section
open Module
open scoped TensorProduct
namespace Representation.BinaryOffender.NaturalTensor
variable (F : Type*) [Field F] [Algebra (ZMod 2) F] [Finite F]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- All binary realizations of a sum of natural modules, allowing summand mixing. -/
theorem natural_sum_inner_bound [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ g v, e (ρ g v) = naturalSumAction F ι g (e v))
    (T : Module.End (ZMod 2) V) (hTi : Function.Injective T)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (r * g * r⁻¹) (T v)) :
    Fintype.card ι * n ≤ operatorFixedCodim T := by
  have h := inner_bound_of_realization ρ
    (e.trans ((naturalSumCoordinates F ι).restrictScalars (ZMod 2)))
    (fun g v => by simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      he, naturalSumCoordinates_action]) T hTi r hr hne hT
  simpa [Module.finrank_pi_fintype, finrank_field F hF] using h

/-- A field twist gives the same bound for every intertwiner of a natural sum. -/
theorem natural_sum_field_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ g v, e (ρ g v) = naturalSumAction F ι g (e v))
    (T : Module.End (ZMod 2) V)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F) (hσ : ∃ a, σ a ≠ a)
    (hT : ∀ g v, T (ρ g v) = ρ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) (T v)) :
    Fintype.card ι * n ≤ operatorFixedCodim T := by
  have h := field_bound_of_realization ρ
    (e.trans ((naturalSumCoordinates F ι).restrictScalars (ZMod 2)))
    (fun g v => by simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      he, naturalSumCoordinates_action]) T r σ hσ hT
  simpa [Module.finrank_pi_fintype, finrank_field F hF] using h

/-- The first factor of the genuine tensor square has two natural summands. -/
theorem tensor_inner_bound [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] TensorSpace F)
    (he : ∀ g v, e (ρ g v) = tensorAction F (g, 1) (e v))
    (T : Module.End (ZMod 2) V) (hTi : Function.Injective T)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (r * g * r⁻¹) (T v)) :
    2 * n ≤ operatorFixedCodim T := by
  have h := inner_bound_of_realization ρ
    (e.trans ((tensorPairCoordinates F).restrictScalars (ZMod 2)))
    (fun g v => by simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      he, tensorPairCoordinates_first]) T hTi r hr hne hT
  simpa only [finrank_natural F hF] using h

/-- A field automorphism on one preserved factor suffices, with arbitrary action
on the other factor and arbitrary compatible twists. -/
theorem tensor_field_intertwiner_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] TensorSpace F)
    (he : ∀ g v, e (ρ g v) = tensorAction F (g, 1) (e v))
    (T : Module.End (ZMod 2) V)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F) (hσ : ∃ a, σ a ≠ a)
    (hT : ∀ g v, T (ρ g v) = ρ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) (T v)) :
    2 * n ≤ operatorFixedCodim T := by
  have h := field_bound_of_realization ρ
    (e.trans ((tensorPairCoordinates F).restrictScalars (ZMod 2)))
    (fun g v => by simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      he, tensorPairCoordinates_first]) T r σ hσ hT
  simpa only [finrank_natural F hF] using h

/-- Exchanging two disjoint natural summands moves an entire natural module. -/
theorem moved_natural_summand_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (T : Module.End (ZMod 2) V) (U : Submodule (ZMod 2) V)
    (e : NaturalSpace F ≃ₗ[ZMod 2] U) (hU : Disjoint U (U.map T)) :
    2 * n ≤ operatorFixedCodim T := by
  have h := finrank_le_operatorFixedCodim_of_disjoint T U hU
  rw [← e.finrank_eq, finrank_natural F hF] at h
  exact h
end Representation.BinaryOffender.NaturalTensor
