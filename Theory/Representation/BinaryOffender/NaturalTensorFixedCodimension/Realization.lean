module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Amplified
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Models
import Mathlib.Tactic

/-!
# Equivariant realizations of natural isotypic modules

A binary change of coordinates transfers the complete inner and inner-field
intertwiner bounds. The concrete natural sum and the tensor square are realized
as amplified natural representations; the tensor's second factor is its
multiplicity space. Thus Frobenius-twisted copies may be identified by actual
binary equivariant maps, without imposing preservation of individual summands.

Source: GLS, vol. 2, Theorem 26.24, final paragraph.
-/

@[expose] public section

open Module
open scoped TensorProduct
namespace Representation.BinaryOffender.NaturalTensor

variable {k F M V : Type*} [Field k] [Field F] [Algebra k F]
  [AddCommGroup M] [Module F M] [Module k M] [IsScalarTower k F M]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V] [FiniteDimensional k M]

omit [Algebra k F] [IsScalarTower k F M] [FiniteDimensional k V] [FiniteDimensional k M] in
lemma conjugate_intertwines (ρ : Representation k (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[k] (M × M))
    (he : ∀ g v, e (ρ g v) = amplifiedNatural g (e v))
    (T : Module.End k V) (α : Matrix.SpecialLinearGroup (Fin 2) F →
      Matrix.SpecialLinearGroup (Fin 2) F)
    (hT : ∀ g v, T (ρ g v) = ρ (α g) (T v)) :
    ∀ g v, e.conj T (amplifiedNatural g v) = amplifiedNatural (α g) (e.conj T v) := by
  intro g v
  simp only [LinearEquiv.conj_apply_apply]
  have hh : e.symm (amplifiedNatural g v) = ρ g (e.symm v) := by
    apply e.injective
    simp [he]
  rw [hh, hT, he]

/-- Bounds for every realization of an amplified natural inner action. -/
theorem inner_bound_of_realization [CharP F 2]
    (ρ : Representation k (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[k] (M × M)) (he : ∀ g v, e (ρ g v) = amplifiedNatural g (e v))
    (T : Module.End k V) (hTi : Function.Injective T)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (r * g * r⁻¹) (T v)) :
    finrank k M ≤ operatorFixedCodim T := by
  have hh := amplified_inner_bound (e.conj T)
    (e.injective.comp (hTi.comp e.symm.injective)) r hr hne
    (conjugate_intertwines ρ e he T _ hT)
  have hc := operatorFixedCodim_eq_of_equiv T (e.conj T) e (by simp)
  omega

/-- Bounds for every realization of an amplified natural inner-field action. -/
theorem field_bound_of_realization
    (ρ : Representation k (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[k] (M × M)) (he : ∀ g v, e (ρ g v) = amplifiedNatural g (e v))
    (T : Module.End k V) (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F)
    (hσ : ∃ a, σ a ≠ a)
    (hT : ∀ g v, T (ρ g v) = ρ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) (T v)) :
    finrank k M ≤ operatorFixedCodim T := by
  have hs := amplified_inner_field_semilinear (e.conj T) r σ
    (conjugate_intertwines ρ e he T _ hT)
  have hh := finrank_le_twice_operatorFixedCodim (e.conj T) σ hσ hs
  rw [Module.finrank_prod] at hh
  have hc := operatorFixedCodim_eq_of_equiv T (e.conj T) e (by simp)
  omega

section Coordinates
variable (F) (ι : Type*)

/-- Regroup a sum of natural modules by its two natural coordinates. -/
def naturalSumCoordinates : (ι → NaturalSpace F) ≃ₗ[F] ((ι → F) × (ι → F)) where
  toFun v := (fun i => v i 0, fun i => v i 1)
  invFun v := fun i => ![v.1 i, v.2 i]
  left_inv v := by ext i j; fin_cases j <;> rfl
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma naturalSumCoordinates_apply (v : ι → NaturalSpace F) :
    naturalSumCoordinates F ι v = (fun i => v i 0, fun i => v i 1) := rfl

/-- The literal componentwise natural SL₂ representation. -/
def naturalSumAction : Representation F (Matrix.SpecialLinearGroup (Fin 2) F)
    (ι → NaturalSpace F) where
  toFun g := LinearMap.pi (fun i => (specialLinearNatural 2 g).comp (LinearMap.proj i))
  map_one' := by ext v i j; simp
  map_mul' g h := by ext v i j; simp

lemma naturalSumAction_apply (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : ι → NaturalSpace F) (i : ι) :
    naturalSumAction F ι g v i = specialLinearNatural 2 g (v i) := rfl

lemma naturalSumCoordinates_action (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : ι → NaturalSpace F) :
    naturalSumCoordinates F ι (naturalSumAction F ι g v) =
      amplifiedNatural g (naturalSumCoordinates F ι v) := by
  apply Prod.ext <;> ext i <;>
    simp [naturalSumCoordinates_apply, naturalSumAction_apply, specialLinearNatural_apply,
      amplifiedNatural_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Tensor coordinates regard the second natural factor as the multiplicity space. -/
def tensorPairCoordinates : TensorSpace F ≃ₗ[F] (NaturalSpace F × NaturalSpace F) :=
  (tensorCoordinates F).trans (naturalSumCoordinates F (Fin 2))

lemma tensorPairCoordinates_first (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : TensorSpace F) :
    tensorPairCoordinates F (tensorAction F (g, 1) v) =
      amplifiedNatural g (tensorPairCoordinates F v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    apply Prod.ext <;> ext i <;>
      simp [tensorPairCoordinates, tensorCoordinates, naturalSumCoordinates_apply, tensorAction,
        specialLinearNatural_apply, amplifiedNatural_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> ring
  | add x y hx hy => simp only [map_add, hx, hy]

end Coordinates
end Representation.BinaryOffender.NaturalTensor
