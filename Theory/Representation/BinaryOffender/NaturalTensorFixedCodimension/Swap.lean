module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Models
import Mathlib.Tactic

/-!
# General twisted intertwiners swapping two natural tensor factors

The line Fe₀ ⊗ e₁ is fixed by a lower root element in the second factor.
A swapping intertwiner sends its fixed vectors to fixed vectors of the lower
root in the first factor. No nonzero vector on that line has both properties.
Consequently displacement embeds an entire copy of F. The proof allows arbitrary
field twists on both exchanged factors and does not assume an operator matrix.

Source: GLS, vol. 2, Theorem 26.24, final contradiction.
-/

@[expose] public section

open Module
open scoped TensorProduct
namespace Representation.BinaryOffender.NaturalTensor
variable (F : Type*) [Field F] [Algebra (ZMod 2) F] [Finite F]

/-- Every twisted factor-swap intertwiner has the required displacement,
not just the coordinate flip. -/
theorem swap_second_factor_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (T : Module.End (ZMod 2) (TensorSpace F)) (σ : F →+* F)
    (hT : ∀ g v, T (tensorAction F (1, g) v) =
      tensorAction F (Matrix.SpecialLinearGroup.map σ g, 1) (T v)) :
    n ≤ operatorFixedCodim T := by
  let : FiniteDimensional (ZMod 2) (TensorSpace F) := Module.Finite.trans F (TensorSpace F)
  let e₀ : NaturalSpace F := Pi.single 0 1
  let e₁ : NaturalSpace F := Pi.single 1 1
  let l : Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero 1
  have hs : Matrix.SpecialLinearGroup.map σ l = l := by
    apply Subtype.ext
    ext i j
    change σ (l.val i j) = l.val i j
    fin_cases i <;> fin_cases j <;> simp [l, Matrix.SpecialLinearGroup.transvection_coe]
  let j : F →ₗ[F] TensorSpace F :=
    (TensorProduct.mk F (NaturalSpace F) (NaturalSpace F) e₀).comp
      (LinearMap.toSpanSingleton F (NaturalSpace F) e₁)
  have hj (a : F) : j a = e₀ ⊗ₜ[F] (a • e₁) := rfl
  have hl : specialLinearNatural 2 l e₁ = e₁ := by
    ext i
    fin_cases i <;> simp [specialLinearNatural_apply, l, e₁,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hjl (a : F) : tensorAction F (1, l) (j a) = j a := by
    rw [hj]
    simp [tensorAction, hl]
  let f : F →ₗ[ZMod 2] LinearMap.range (T - 1) :=
    ((T - 1).comp (j.restrictScalars (ZMod 2))).codRestrict _ (fun a => ⟨j a, rfl⟩)
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro a ha
    have ht : T (j a) = j a := by
      have hh := congrArg Subtype.val (show f a = 0 from ha)
      exact sub_eq_zero.mp hh
    have hh := hT l (j a)
    rw [hjl, ht, hs] at hh
    have hc := congrArg (fun z => tensorCoordinates F z 1 1) hh
    simpa [hj, tensorAction, tensorCoordinates_tmul, specialLinearNatural_apply,
      l, e₀, e₁, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hc.symm
  rw [← finrank_field F hF]
  exact LinearMap.finrank_le_finrank_of_injective hi

/-- General field twists on both exchanged factors are permitted. -/
theorem swap_intertwiner_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (T : Module.End (ZMod 2) (TensorSpace F)) (σ τ : F →+* F)
    (hT : ∀ g v, T (tensorAction F g v) =
      tensorAction F (Matrix.SpecialLinearGroup.map σ g.2,
        Matrix.SpecialLinearGroup.map τ g.1) (T v)) :
    n ≤ operatorFixedCodim T :=
  swap_second_factor_bound F hF T σ (fun g v => by simpa using hT (1, g) v)

/-- Inner twists on the exchanged factors are removed by an actual change
of tensor coordinates. Only the intertwining of the second factor is needed. -/
theorem swap_inner_field_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (T : Module.End (ZMod 2) (TensorSpace F))
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F)
    (hT : ∀ g v, T (tensorAction F (1, g) v) =
      tensorAction F (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹, 1) (T v)) :
    n ≤ operatorFixedCodim T := by
  let : FiniteDimensional (ZMod 2) (TensorSpace F) := Module.Finite.trans F (TensorSpace F)
  let e : TensorSpace F ≃ₗ[ZMod 2] TensorSpace F :=
    { (tensorAction F (r⁻¹, 1)).restrictScalars (ZMod 2) with
      invFun := tensorAction F (r, 1)
      left_inv := fun v => by
        change tensorAction F (r, 1) (tensorAction F (r⁻¹, 1) v) = v
        simp only [← Module.End.mul_apply, ← map_mul]
        simp only [Prod.mk_mul_mk, mul_inv_cancel, one_mul]
        change tensorAction F 1 v = v
        rw [map_one]
        rfl
      right_inv := fun v => by
        change tensorAction F (r⁻¹, 1) (tensorAction F (r, 1) v) = v
        simp only [← Module.End.mul_apply, ← map_mul]
        simp only [Prod.mk_mul_mk, inv_mul_cancel, one_mul]
        change tensorAction F 1 v = v
        rw [map_one]
        rfl }
  have hh : ∀ g v, e.conj T (tensorAction F (1, g) v) =
      tensorAction F (Matrix.SpecialLinearGroup.map σ g, 1) (e.conj T v) := by
    intro g v
    change tensorAction F (r⁻¹, 1) (T (tensorAction F (r, 1)
      (tensorAction F (1, g) v))) =
      tensorAction F (Matrix.SpecialLinearGroup.map σ g, 1)
        (tensorAction F (r⁻¹, 1) (T (tensorAction F (r, 1) v)))
    have hc : tensorAction F (r, 1) (tensorAction F (1, g) v) =
        tensorAction F (1, g) (tensorAction F (r, 1) v) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hc, hT]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    ext <;> simp [mul_assoc]
  have hb := swap_second_factor_bound F hF (e.conj T) σ hh
  have he := operatorFixedCodim_eq_of_equiv T (e.conj T) e (by simp)
  omega

/-- The twisted-swap bound in any binary equivariant realization of the tensor. -/
theorem swap_bound_of_realization {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] TensorSpace F)
    (he : ∀ g v, e (ρ g v) = tensorAction F g (e v))
    (T : Module.End (ZMod 2) V)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F)
    (hT : ∀ g v, T (ρ (1, g) v) =
      ρ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹, 1) (T v)) :
    n ≤ operatorFixedCodim T := by
  let : FiniteDimensional (ZMod 2) (TensorSpace F) := Module.Finite.trans F (TensorSpace F)
  have hh : ∀ g v, e.conj T (tensorAction F (1, g) v) =
      tensorAction F (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹, 1) (e.conj T v) := by
    intro g v
    have hs : e.symm (tensorAction F (1, g) v) = ρ (1, g) (e.symm v) := by
      apply e.injective
      simp [he]
    simp only [LinearEquiv.conj_apply_apply, hs, hT, he]
  have hb := swap_inner_field_bound F hF (e.conj T) r σ hh
  have hc := operatorFixedCodim_eq_of_equiv T (e.conj T) e (by simp)
  omega

end Representation.BinaryOffender.NaturalTensor
