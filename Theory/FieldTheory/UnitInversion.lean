module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
public import Mathlib.GroupTheory.Exponent

/-!
# Field automorphisms cannot invert a large binary unit group

If a field automorphism inverts every unit, applying additivity at x+1
forces every unit to have cube one. Cyclicity of the unit group then gives
at most four field elements. Thus inverse field action is nontrivial over
any binary field larger than four.

The automorphism group of a cyclic unit group is abelian. Thus two
multiplicative markings cannot make the same group automorphism appear as
both inverse field action and ordinary field action when the field has
more than four elements.

The original Cartan exchanger uses this to exclude the centralizing case
without assuming the Sylow exchanger is an involution.
Source: Aschbacher--Smith 9.2.7, pp.731--732, refs/quasithin.pdf.
-/

public noncomputable section
namespace FiniteField
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem card_le_four_of_ringAut_inverts_units (σ : F ≃+* F)
    (hσ : ∀ z : Fˣ, Units.map σ.toMonoidHom z = z⁻¹) : Nat.card F ≤ 4 := by
  have hf (x : F) (hx : x ≠ 0) : σ x = x⁻¹ := by
    have hh := congrArg Units.val (hσ (Units.mk0 x hx))
    change σ x = (↑((Units.mk0 x hx)⁻¹) : F) at hh
    simpa only [Units.val_inv_eq_inv_val,Units.val_mk0] using hh
  have hc (z : Fˣ) : z^3 = 1 := by
    by_cases hz : (z:F) = 1
    · apply Units.ext
      simp [hz]
    · have hx : (z:F)+1 ≠ 0 := by
        intro h
        apply hz
        simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
      have hh : ((z:F)+1)⁻¹ = (z:F)⁻¹+1 := by
        rw [←hf _ hx,map_add,hf _ z.ne_zero,map_one]
      have he : (1:F) = ((z:F)+1)^2 / (z:F) := by
        calc
          1 = ((z:F)+1) * ((z:F)+1)⁻¹ := (mul_inv_cancel₀ hx).symm
          _ = ((z:F)+1) * ((z:F)⁻¹+1) := by rw [hh]
          _ = ((z:F)+1)^2 / (z:F) := by field_simp; ring
      have he' := (eq_div_iff z.ne_zero).mp he
      have hp : (z:F)^2+(z:F)+1 = 0 := by
        linear_combination -he'
      apply Units.ext
      change (z:F)^3 = 1
      linear_combination ((z:F)-1)*hp
  have hd : Nat.card Fˣ ∣ 3 := by
    rw [←IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hc
  have hb := Nat.le_of_dvd (by decide : 0 < 3) hd
  rw [Nat.card_units] at hb
  omega

theorem exists_unit_not_inverted (hF : 4 < Nat.card F) (σ : F ≃+* F) :
    ∃ z : Fˣ, Units.map σ.toMonoidHom z ≠ z⁻¹ := by
  by_contra! h
  exact (not_lt_of_ge (card_le_four_of_ringAut_inverts_units σ h)) hF

variable {B : Type*} [Group B]

/-- Arbitrary multiplicative markings of a cyclic unit group do not conceal
an inverse field action: over a field larger than four it cannot also be
an ordinary field action. -/
theorem inverse_field_action_not_field (hF : 4 < Nat.card F)
    (χ : B ≃* Fˣ) (β : MulAut B) (σ : F ≃+* F)
    (hβ : ∀ b, χ (β b) = (Units.map σ.toMonoidHom (χ b))⁻¹)
    (ψ : B ≃* Fˣ) (τ : F ≃+* F)
    (hψ : ∀ b, ψ (β b) = Units.map τ.toMonoidHom (ψ b)) : False := by
  let c : MulAut Fˣ := χ.symm.trans ψ
  let τu : MulAut Fˣ := Units.mapEquiv τ.toMulEquiv
  have hc : c * τu = τu * c := (IsCyclic.mulAutMulEquiv Fˣ).injective (by
    rw [map_mul,map_mul,mul_comm])
  have hcomm (z : Fˣ) : c (Units.map τ.toMonoidHom z) =
      Units.map τ.toMonoidHom (c z) := MulEquiv.congr_fun hc z
  have hτ (z : Fˣ) : Units.map τ.toMonoidHom z = (Units.map σ.toMonoidHom z)⁻¹ := by
    obtain ⟨b,rfl⟩ := χ.surjective z
    apply c.injective
    rw [hcomm,←hβ]
    change Units.map τ.toMonoidHom (ψ (χ.symm (χ b))) = ψ (χ.symm (χ (β b)))
    rw [χ.symm_apply_apply,χ.symm_apply_apply,hψ]
  apply (not_lt_of_ge (card_le_four_of_ringAut_inverts_units (σ.symm.trans τ) ?_)) hF
  intro z
  have hh := hτ (Units.map σ.symm.toMonoidHom z)
  apply Units.ext
  have hh' := congrArg Units.val hh
  change τ (σ.symm (z:F)) = (↑((Units.map σ.toMonoidHom
    (Units.map σ.symm.toMonoidHom z))⁻¹) : F) at hh'
  rw [Units.val_inv_eq_inv_val] at hh'
  change τ (σ.symm (z:F)) = (σ (σ.symm (z:F)))⁻¹ at hh'
  rw [σ.apply_symm_apply] at hh'
  change τ (σ.symm (z:F)) = (↑(z⁻¹):F)
  simpa only [Units.val_inv_eq_inv_val] using hh'

end FiniteField
