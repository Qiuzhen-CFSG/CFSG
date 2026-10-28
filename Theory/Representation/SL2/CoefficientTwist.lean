module

public import Theory.Representation.SL2.HighestWeightSpan
public import Theory.LinearAlgebra.SemilinearTrace
public import Mathlib.RepresentationTheory.Character

/-!
# Coefficient Automorphisms and Highest-Weight Characters

For an embedding of fields K into F, changing that embedding by an automorphism
of F applies the same automorphism to the character of the actual highest-weight
orbit span. Neither finiteness of K nor a bound on the degree is needed.

Applying the automorphism coefficientwise commutes with matrix substitution
and sends orbit generators to the corresponding generators for the new
embedding. It therefore restricts to a semilinear equivalence of the actual
orbit spans; the inverse coefficient map proves bijectivity. Its intertwining
relation identifies the conjugated endomorphism, and semilinear invariance of
trace gives the character formula.

This is the coefficient-twist step in the Frobenius-period argument following
Fong--Wong (1.15), Nagoya Math. J. 36 (1969), p. 149.
-/

open MvPolynomial
open scoped MatrixGroups

namespace Representation.SL2

variable {K F : Type*} [Field K] [Field F]

private theorem coefficient_map_smul (σ : F →+* F) (a : F) (f : MvPolynomial (Fin 2) F) :
    MvPolynomial.map σ (a • f) = σ a • MvPolynomial.map σ f := by
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, MvPolynomial.map_C]

private theorem coefficient_map_action (σ : F →+* F) (e : K →+* F)
    (g : SL(2,K)) (f : MvPolynomial (Fin 2) F) :
    MvPolynomial.map σ (polynomialAction F (Matrix.SpecialLinearGroup.map e g) f) =
      polynomialAction F (Matrix.SpecialLinearGroup.map (σ.comp e) g) (MvPolynomial.map σ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [polynomialAction]
  | add f h hf hh => simp [hf, hh]
  | mul_X f i hf =>
    simp only [map_mul, hf]
    congr 1
    simp [polynomialAction]

private theorem coefficient_map_mem (σ : F →+* F) (e : K →+* F) (n : ℕ)
    (f : MvPolynomial (Fin 2) F) (hf : f ∈ highestWeightSpan e n) :
    MvPolynomial.map σ f ∈ highestWeightSpan (σ.comp e) n := by
  change f ∈ Submodule.span F _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    rw [coefficient_map_action]
    simp only [map_pow, MvPolynomial.map_X]
    exact Submodule.subset_span ⟨g, map_pow _ _ _⟩
  | zero => simp only [map_zero]; exact (highestWeightSpan (σ.comp e) n).toSubmodule.zero_mem
  | add f h _ _ hf hh =>
    rw [map_add]
    exact (highestWeightSpan (σ.comp e) n).toSubmodule.add_mem hf hh
  | smul a f _ hf =>
    rw [coefficient_map_smul]
    exact (highestWeightSpan (σ.comp e) n).toSubmodule.smul_mem (σ a) hf

variable (σ : F ≃+* F)

private theorem coefficient_map_symm_mem (e : K →+* F) (n : ℕ)
    (f : MvPolynomial (Fin 2) F) (hf : f ∈ highestWeightSpan ((σ : F →+* F).comp e) n) :
    MvPolynomial.map (σ.symm : F →+* F) f ∈ highestWeightSpan e n := by
  have h := coefficient_map_mem (σ.symm : F →+* F) ((σ : F →+* F).comp e) n f hf
  have he : (σ.symm : F →+* F).comp ((σ : F →+* F).comp e) = e := by ext a; simp
  rw [he] at h
  exact h

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private noncomputable def coefficientMapEquiv (e : K →+* F) (n : ℕ) :
    LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F))
      (highestWeightSpan e n).toSubmodule
      (highestWeightSpan ((σ : F →+* F).comp e) n).toSubmodule where
  toFun f := ⟨MvPolynomial.map (σ : F →+* F) f, coefficient_map_mem (σ : F →+* F) e n f f.property⟩
  invFun f := ⟨MvPolynomial.map (σ.symm : F →+* F) f, coefficient_map_symm_mem σ e n f f.property⟩
  left_inv f := by
    apply Subtype.ext
    simp only [MvPolynomial.map_map, RingEquiv.symm_comp, MvPolynomial.map_id]
  right_inv f := by
    apply Subtype.ext
    simp only [MvPolynomial.map_map, RingEquiv.comp_symm, MvPolynomial.map_id]
  map_add' f h := Subtype.ext (map_add _ _ _)
  map_smul' a f := Subtype.ext (coefficient_map_smul _ _ _)

private theorem coefficientMapEquiv_intertwines (e : K →+* F) (n : ℕ) (g : SL(2,K))
    (f : (highestWeightSpan e n).toSubmodule) :
    coefficientMapEquiv σ e n ((highestWeightSpan e n).toRepresentation g f) =
      (highestWeightSpan ((σ : F →+* F).comp e) n).toRepresentation g
        (coefficientMapEquiv σ e n f) := by
  apply Subtype.ext
  exact coefficient_map_action (σ : F →+* F) e g f

public theorem highestWeightSpan_character_comp_embedding (e : K →+* F) (n : ℕ) (g : SL(2,K)) :
    (highestWeightSpan ((σ : F →+* F).comp e) n).toRepresentation.character g =
      σ ((highestWeightSpan e n).toRepresentation.character g) := by
  have h := LinearMap.trace_conj_semilinear σ
    ((highestWeightSpan e n).toRepresentation g) (coefficientMapEquiv σ e n)
  have he : (coefficientMapEquiv σ e n).conj ((highestWeightSpan e n).toRepresentation g) =
      (highestWeightSpan ((σ : F →+* F).comp e) n).toRepresentation g := by
    ext f
    rw [LinearEquiv.conj_apply_apply, coefficientMapEquiv_intertwines,
      LinearEquiv.apply_symm_apply]
  rw [he] at h
  exact h

end Representation.SL2
