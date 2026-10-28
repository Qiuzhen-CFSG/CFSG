module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.EndFieldFrobenius

/-!
# Coefficient automorphisms of the concrete SL₃ tensor factors

A coefficient automorphism acts semilinearly on the natural space and, by
conjugation, on its trace-zero endomorphisms. These actual semilinear maps
intertwine the corresponding actions. The semilinear trace formula, the dual
character formula and multiplicativity of tensor characters then identify
the characters of all four defining factors and their tensor words after a
change of coefficient embedding.

This is the coefficient calculation in GLS III, Remark 2.8.8. No catalogue
or irreducibility assertion is needed for these identities.
-/

public section

open scoped MatrixGroups TensorProduct MonoidAlgebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.SL3.BinaryDefiningFactors
variable {F K : Type*} [Field F] [Field K]
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private theorem natural_coefficients (σ : K ≃+* K) (ι : F →+* K)
    (g : SL(3,F)) (v : Fin 3 → K) :
    coordinateSemilinearEquiv σ (Fin 3) (natural ι g v) =
      natural ((σ : K →+* K).comp ι) g (coordinateSemilinearEquiv σ (Fin 3) v) := by
  ext i
  rw [coordinateSemilinearEquiv_apply]
  change σ (∑ j, ι (g.val i j) * v j) =
    ∑ j, σ (ι (g.val i j)) * coordinateSemilinearEquiv σ (Fin 3) v j
  simp

private theorem natural_conj (σ : K ≃+* K) (ι : F →+* K) (g : SL(3,F)) :
    (coordinateSemilinearEquiv σ (Fin 3)).conj (natural ι g) =
      natural ((σ : K →+* K).comp ι) g := by
  apply LinearMap.ext
  intro v
  have h := natural_coefficients σ ι g ((coordinateSemilinearEquiv σ (Fin 3)).symm v)
  simpa using h

private def adjointCoefficientEquiv (σ : K ≃+* K) :
    LinearEquiv (σ : K →+* K) (σ' := (σ.symm : K →+* K))
      (AdjointSpace K) (AdjointSpace K) where
  toFun f := ⟨(coordinateSemilinearEquiv σ (Fin 3)).conj f, by
    change LinearMap.trace K _ ((coordinateSemilinearEquiv σ (Fin 3)).conj f) = 0
    rw [LinearMap.trace_conj_semilinear]
    exact (map_eq_zero σ).mpr f.property⟩
  invFun f := ⟨(coordinateSemilinearEquiv σ (Fin 3)).symm.conj f, by
    change LinearMap.trace K _ ((coordinateSemilinearEquiv σ (Fin 3)).symm.conj f) = 0
    rw [LinearMap.trace_conj_semilinear σ.symm]
    exact (map_eq_zero σ.symm).mpr f.property⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv f := by apply Subtype.ext; simp
  map_add' f h := Subtype.ext (map_add _ _ _)
  map_smul' c f := Subtype.ext (map_smulₛₗ _ _ _)

private def adjointAction (ι : F →+* K) (g : SL(3,F)) : Module.End K (AdjointSpace K) :=
  (traceZero ι).toRepresentation g

private theorem adjoint_coefficients (σ : K ≃+* K) (ι : F →+* K)
    (g : SL(3,F)) (f : AdjointSpace K) :
    adjointCoefficientEquiv σ (adjointAction ι g f) =
      adjointAction ((σ : K →+* K).comp ι) g (adjointCoefficientEquiv σ f) := by
  apply Subtype.ext
  change (coordinateSemilinearEquiv σ (Fin 3)).conj
      (natural ι g ∘ₗ f.val ∘ₗ natural ι g⁻¹) =
    natural ((σ : K →+* K).comp ι) g ∘ₗ
      (coordinateSemilinearEquiv σ (Fin 3)).conj f.val ∘ₗ
        natural ((σ : K →+* K).comp ι) g⁻¹
  rw [LinearEquiv.conj_comp, LinearEquiv.conj_comp, natural_conj, natural_conj]

/-- Changing the coefficient embedding applies the automorphism to each actual factor character. -/
theorem factorRep_character_comp (σ : K ≃+* K) (ι : F →+* K)
    (a : Factor) (g : SL(3,F)) :
    (factorRep ((σ : K →+* K).comp ι) a).character g =
      σ ((factorRep ι a).character g) := by
  have hn (g : SL(3,F)) :
      (natural ((σ : K →+* K).comp ι)).character g = σ ((natural ι).character g) := by
    change LinearMap.trace K _ _ = σ (LinearMap.trace K _ _)
    simpa only [natural_conj] using
      LinearMap.trace_conj_semilinear σ (natural ι g) (coordinateSemilinearEquiv σ (Fin 3))
  cases a with
  | trivial =>
    change LinearMap.trace K K 1 = σ (LinearMap.trace K K 1)
    simp
  | natural => exact hn g
  | dual =>
    change (natural ((σ : K →+* K).comp ι)).dual.character g =
      σ ((natural ι).dual.character g)
    simpa only [char_dual] using hn g⁻¹
  | adjoint =>
    change LinearMap.trace K (AdjointSpace K) (adjointAction ((σ : K →+* K).comp ι) g) =
      σ (LinearMap.trace K (AdjointSpace K) (adjointAction ι g))
    have he : (adjointCoefficientEquiv σ).conj (adjointAction ι g) =
        adjointAction ((σ : K →+* K).comp ι) g := by
      apply LinearMap.ext
      intro f
      rw [LinearEquiv.conj_apply_apply, adjoint_coefficients, LinearEquiv.apply_symm_apply]
    change LinearMap.trace K (AdjointSpace K) _ = σ (LinearMap.trace K (AdjointSpace K) _)
    rw [← he]
    exact LinearMap.trace_conj_semilinear (V := AdjointSpace K) (W := AdjointSpace K)
      σ (adjointAction ι g)
      (adjointCoefficientEquiv σ)

variable [CharP K 2]

@[simp] theorem wordRep_character_nil (ι : F →+* K) (g : SL(3,F)) :
    (wordRep ι []).character g = 1 := by
  change LinearMap.trace K K 1 = 1
  simp

theorem wordRep_character_cons (ι : F →+* K) (a : Factor) (w : List Factor)
    (g : SL(3,F)) :
    (wordRep ι (a :: w)).character g =
      (factorRep ι a).character g * (wordRep ((frobenius K 2).comp ι) w).character g := by
  change ((factorRep ι a).tprod (wordRep ((frobenius K 2).comp ι) w)).character g = _
  exact congrFun (char_tensor _ _) g

/-- The coefficient formula extends multiplicatively to the concrete tensor word. -/
theorem wordRep_character_comp (σ : K ≃+* K) (ι : F →+* K)
    (w : List Factor) (g : SL(3,F)) :
    (wordRep ((σ : K →+* K).comp ι) w).character g =
      σ ((wordRep ι w).character g) := by
  induction w generalizing ι with
  | nil => simp only [wordRep_character_nil, map_one]
  | cons a w ih =>
    have hc : (frobenius K 2).comp ((σ : K →+* K).comp ι) =
        (σ : K →+* K).comp ((frobenius K 2).comp ι) := by
      ext x
      change σ (ι x) ^ 2 = σ ((ι x) ^ 2)
      exact (map_pow σ _ _).symm
    simp only [wordRep_character_cons, factorRep_character_comp, hc, ih, map_mul]



end Representation.SL3.BinaryDefiningFactors
