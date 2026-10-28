module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Model
public import Theory.Representation.QuadraticFourGroup.TensorClassification.FixedPoints
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Mathlib.LinearAlgebra.TensorProduct.Basis
/-!
# Excluding mixed factors under the original exchange

An actual linear exchange transfers cubic freeness between the two marked
factors. The deleted five-letter core has a nonzero cubic fixed vector;
tensor contractions preserve cubic freeness of the other factor. Thus a
deleted/cubic-free mixed tensor cannot have the source exchanging actor.
This is the mixed-constituent exclusion in Aschbacher–Smith D.3.7,
printed pp.197–199, retaining the literal exchange and automorphism marking.
-/
public section
open scoped TensorProduct
open Representation Representation.QuadraticFourGroup.TensorClassification
namespace BinaryPermutation.FiveTensorSquare
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- An actual exchange transfers cubic freeness from the second factor to
the first, including arbitrary automorphisms in the factor marking. -/
theorem cubic_free_left_of_exchange
    (ρ : Representation (ZMod 2) (Alt × Alt) U)
    (e : U ≃ₗ[ZMod 2] U) (α : MulAut Alt)
    (he : ∀ g v, e (ρ (g,1) v) = ρ (1,α g) (e v))
    (hfree : ∀ g, orderOf g = 3 → FixedPointFreeAt ρ (1,g)) :
    ∀ g, orderOf g = 3 → FixedPointFreeAt ρ (g,1) := by
  intro g hg v hv
  apply e.injective
  rw [map_zero]
  apply hfree (α g) ((orderOf_injective α.toMonoidHom α.injective g).trans hg)
  rw [←he,hv]

private theorem right_fixed_of_factor (σ : Representation (ZMod 2) Alt U)
    (g : Alt) (hσ : FixedPointFreeAt σ g) :
    FixedPointFreeAt (externalTensor δ σ) (1,g) := by
  intro x hx
  let b := Module.finBasis (ZMod 2) C
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := U) b
  have he (x : C ⊗[ZMod 2] U) (i) :
      e (externalTensor δ σ (1,g) x) i = σ g (e x i) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      change e (δ 1 u ⊗ₜ[ZMod 2] σ g v) i = _
      simp [e]
    | add x y hx hy => simpa only [map_add,Finsupp.add_apply] using congrArg₂ (· + ·) hx hy
  apply e.injective
  apply Finsupp.ext
  intro i
  simpa only [map_zero,Finsupp.zero_apply] using hσ (e x i) (by rw [←he,hx])

/-- A deleted/natural mixed tensor cannot admit the original factor-exchanging
actor. The second factor is characterized by its cubic freeness. -/
theorem no_exchange_deleted_cubic_free [Nontrivial U]
    (σ : Representation (ZMod 2) Alt U) (hσ : CubicFixedPointFree σ)
    (e : (C ⊗[ZMod 2] U) ≃ₗ[ZMod 2] (C ⊗[ZMod 2] U)) (α : MulAut Alt)
    (he : ∀ g v, e (externalTensor δ σ (g,1) v) =
      externalTensor δ σ (1,α g) (e v)) : False := by
  have hf := cubic_free_left_of_exchange (externalTensor δ σ) e α he
    (fun g hg => right_fixed_of_factor σ g (hσ g hg))
  obtain ⟨g,hg,v,hv,hfix⟩ := AlternatingFiveLinearTwo.exists_cubic_fixed_ne_zero
  exact hv ((hf g hg).left_of_externalTensor v hfix)
end BinaryPermutation.FiveTensorSquare
