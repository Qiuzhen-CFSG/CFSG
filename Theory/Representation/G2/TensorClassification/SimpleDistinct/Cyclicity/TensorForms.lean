module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.Cyclicity.FactorForms
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.Cyclicity.PairingCriterion
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.Boundary
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry

/-!
# Pairings on the actual Frobenius tensor words

Tensor the restricted-factor forms and extend scalars. Field transport preserves
the actual unipotent subgroup and fixes the marked Weyl reflections, so the
resulting forms remain unipotent-invariant and pair each specified highest
vector with its longest-Weyl translate with value one. The empty word uses
ordinary field multiplication. No nondegeneracy or tensor simplicity is assumed.

Source: the highest-weight cyclicity step for GLS3, 2.8.6(a) and 2.8.10(g).
-/

public noncomputable section
open scoped TensorProduct
namespace Atlas.G2.TensorClassification.Cyclicity
open Restricted
variable (F : Type*) [Field F] [CharP F 2] [Finite F]

private theorem frobenius_unipotent_mem (r : ℕ) (g : Model F) (hg : g ∈ unipotent) :
    frobeniusAutomorphism F r g ∈ unipotent := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  change fieldEquiv (iterateFrobeniusEquiv F 2 r) (unipotentProduct t) ∈ unipotent
  rw [LieParabolicSetup.long_field_unipotentProduct]
  exact unipotentProduct_mem _

private theorem factorRep_longest (r : ℕ) (a : Factor) :
    factorRep F r a (Steinberg.longestWeyl F) = action F a (Steinberg.longestWeyl F) := by
  change factorRep F r a ((simpleReflection F true * simpleReflection F false)^3) =
    action F a ((simpleReflection F true * simpleReflection F false)^3)
  rw [map_pow, map_mul, factorRep_simpleReflection, factorRep_simpleReflection,
    ← map_mul, ← map_pow]

/-- Recursive product of the four actual factor forms. -/
@[expose] def wordForm : (w : List Factor) → LinearMap.BilinForm F (WordSpace F w)
  | [] => LinearMap.mul F F
  | a :: w => (factorForm F a).tmul (wordForm w)

/-- Frobenius-twisted positive-unipotent actions preserve the word form. -/
theorem wordForm_invariant (r : ℕ) (w : List Factor) (g : Model F)
    (hg : g ∈ unipotent) (x y : WordSpace F w) :
    wordForm F w (wordRep F r w g x) (wordRep F r w g y) = wordForm F w x y := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
    exact tensorProductForm_invariant (factorForm F a) (wordForm F w)
      (factorRep F r a g) (wordRep F (r + 1) w g)
      (factorForm_invariant F a _ (frobenius_unipotent_mem F r g hg))
      (ih (r + 1)) x y

/-- The same longest Weyl element gives pairing one at every tensor position. -/
theorem wordForm_opposite_highestVector (r : ℕ) (w : List Factor) :
    wordForm F w (wordRep F r w (Steinberg.longestWeyl F) (wordHighestVector F w))
      (wordHighestVector F w) = 1 := by
  induction w generalizing r with
  | nil => change (1 : F) * 1 = 1; exact one_mul _
  | cons a w ih =>
    change (factorForm F a).tmul (wordForm F w)
      (factorRep F r a (Steinberg.longestWeyl F) (highestVector F a) ⊗ₜ[F]
        wordRep F (r + 1) w (Steinberg.longestWeyl F) (wordHighestVector F w))
      (highestVector F a ⊗ₜ[F] wordHighestVector F w) = 1
    rw [LinearMap.BilinForm.tensorDistrib_tmul, factorRep_longest,
      factorForm_opposite_highestVector, ih, one_smul]

variable (K : Type*) [Field K] [Algebra F K]

/-- Scalar extension of the concrete word form. -/
@[expose] def tensorForm {n : ℕ} (w : Fin n → Factor) : LinearMap.BilinForm K (TensorSpace F K w) :=
  (wordForm F (List.ofFn w)).baseChange K

/-- Positive-unipotent invariance survives scalar extension. -/
theorem tensorForm_invariant {n : ℕ} (w : Fin n → Factor) (g : Model F)
    (hg : g ∈ unipotent) (x y : TensorSpace F K w) :
    tensorForm F K w (tensorRep F K w g x) (tensorRep F K w g y) = tensorForm F K w x y := by
  have he : (tensorForm F K w).compl₁₂ (tensorRep F K w g) (tensorRep F K w g) =
      tensorForm F K w := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a b
    apply TensorProduct.AlgebraTensorModule.ext
    intro c d
    simp [tensorForm, tensorRep, wordForm_invariant F 0 _ g hg]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- Highest and opposite highest vectors pair to one after scalar extension. -/
theorem tensorForm_opposite_highestVector {n : ℕ} (w : Fin n → Factor) :
    tensorForm F K w
      (tensorRep F K w (Steinberg.longestWeyl F) (tensorHighestVector F K w))
      (tensorHighestVector F K w) = 1 := by
  change (wordForm F (List.ofFn w)).baseChange K
    ((1 : K) ⊗ₜ[F] wordRep F 0 (List.ofFn w) (Steinberg.longestWeyl F)
      (wordHighestVector F (List.ofFn w)))
    ((1 : K) ⊗ₜ[F] wordHighestVector F (List.ofFn w)) = 1
  rw [LinearMap.BilinForm.baseChange_tmul, wordForm_opposite_highestVector]
  simp
end Atlas.G2.TensorClassification.Cyclicity
end
