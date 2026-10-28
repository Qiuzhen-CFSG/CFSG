module

public import Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates
public import Theory.Representation.SemilinearConjugation
public import Theory.Representation.ExtendScalars
public import Mathlib.FieldTheory.Perfect

/-!
# Coefficient and Frobenius transport of the actual G₂ adjoint module

Conjugation by coefficient transport on split octonions preserves the Leibniz
identity and gives an invertible semilinear map on derivations. It intertwines
conjugation by g with conjugation by the actual field automorphism image of g.
In the fourteen independent derivation parameters this is entrywise coefficient
transport. The resulting representation equivalence retains arbitrary scalar
extensions and specializes to every iterate of finite-field Frobenius.

Source: GLS3, Definition 2.8.3, Remark 2.8.8 and Example 2.8.10(g).
-/

@[expose] public noncomputable section

namespace Atlas.G2.Restricted.Adjoint
open Atlas.SplitOctonion
variable (F : Type*) [Field F]
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
/-- Coefficient conjugation on the ambient endomorphisms. -/
def coefficientEndomorphism (σ : F ≃+* F) (D : Module.End F (Carrier F)) :
    Module.End F (Carrier F) where
  toFun x := mapCoefficients σ (D (mapCoefficients σ.symm x))
  map_add' x y := by simp
  map_smul' a x := by simp
@[simp] theorem coefficientEndomorphism_apply (σ : F ≃+* F)
    (D : Module.End F (Carrier F)) (x : Carrier F) :
    coefficientEndomorphism F σ D x = mapCoefficients σ (D (mapCoefficients σ.symm x)) := rfl
/-- Integral octonion multiplication ensures preservation of Leibniz. -/
theorem coefficientEndomorphism_mem (σ : F ≃+* F) (D : Space F) :
    coefficientEndomorphism F σ D.val ∈ derivations F := by
  intro x y
  simp only [coefficientEndomorphism_apply, mapCoefficients_mul, leibniz,
    mapCoefficients_add, mapCoefficients_symm]
/-- Genuine semilinear coefficient transport on octonion derivations. -/
def coefficientSemilinearEquiv (σ : F ≃+* F) :
    LinearEquiv (σ : F →+* F) (σ' := (σ.symm : F →+* F)) (Space F) (Space F) where
  toFun D := ⟨coefficientEndomorphism F σ D.val, coefficientEndomorphism_mem F σ D⟩
  invFun D := ⟨coefficientEndomorphism F σ.symm D.val, coefficientEndomorphism_mem F σ.symm D⟩
  left_inv D := by
    apply Subtype.ext
    ext x
    simp
  right_inv D := by
    apply Subtype.ext
    ext x
    simp
  map_add' D E := by
    apply Subtype.ext
    ext x
    simp
  map_smul' a D := by
    apply Subtype.ext
    ext x
    simp
@[simp] theorem coefficientSemilinearEquiv_apply (σ : F ≃+* F) (D : Space F)
    (x : Carrier F) :
    (coefficientSemilinearEquiv F σ D).val x =
      mapCoefficients σ (D.val (mapCoefficients σ.symm x)) := rfl
/-- Coefficient transport intertwines the actual group field automorphism. -/
theorem coefficientSemilinearEquiv_action (σ : F ≃+* F) (g : Model F) (D : Space F) :
    coefficientSemilinearEquiv F σ (action F g D) =
      action F (fieldEquiv σ g) (coefficientSemilinearEquiv F σ D) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change mapCoefficients σ (g.val (D.val ((g⁻¹).val (mapCoefficients σ.symm x)))) =
    mapCoefficients σ (g.val (mapCoefficients σ.symm (mapCoefficients σ
      (D.val (mapCoefficients σ.symm (mapCoefficients σ
        ((g⁻¹).val (mapCoefficients σ.symm x))))))))
  simp
/-- Semilinear conjugation is twisting the action by the genuine field automorphism. -/
theorem coefficientConjugate_eq (σ : F ≃+* F) :
    Representation.semilinearConjugate (V := Space F) (W := Space F) σ (action F) (coefficientSemilinearEquiv F σ) =
      (action F).comp (fieldEquiv σ).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro D
  change coefficientSemilinearEquiv F σ
    (action F g ((coefficientSemilinearEquiv F σ).symm D)) = _
  rw [coefficientSemilinearEquiv_action, LinearEquiv.apply_symm_apply]
  rfl
/-- An actual intertwining equivalence, rather than a character equality. -/
def coefficientConjugateEquiv (σ : F ≃+* F) :
    Representation.RepEquiv
      (Representation.semilinearConjugate (V := Space F) (W := Space F) σ (action F) (coefficientSemilinearEquiv F σ))
      ((action F).comp (fieldEquiv σ).toMonoidHom) where
  toLinearEquiv := LinearEquiv.refl F _
  isIntertwining' g := by
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    exact DFunLike.congr_fun (coefficientConjugate_eq F σ) g
/-- The same intertwining equivalence after arbitrary scalar extension. -/
def coefficientConjugateEquiv_extendScalars (K : Type*) [Field K] [Algebra F K]
    (σ : F ≃+* F) :
    Representation.RepEquiv
      (Representation.extendScalars (F := F) (V := Space F) K (Representation.semilinearConjugate (V := Space F) (W := Space F) σ
        (action F) (coefficientSemilinearEquiv F σ)))
      (Representation.extendScalars (F := F) (V := Space F) K ((action F).comp (fieldEquiv σ).toMonoidHom)) := by
  rw [coefficientConjugate_eq]

section CharacteristicTwo
variable [CharP F 2]
/-- In the explicit derivation coordinates, coefficient transport is entrywise. -/
theorem coefficientSemilinearEquiv_coordinates (σ : F ≃+* F) (D : Space F) :
    Coordinates.equiv F (coefficientSemilinearEquiv F σ D) =
      fun i => σ (Coordinates.equiv F D i) := by
  have hb (j : Fin 8) : mapCoefficients σ.symm (basisVector j) = basisVector j := by
    ext k
    simp [mapCoefficients, basisVector, Pi.single_apply, apply_ite]
  ext i
  fin_cases i <;>
    simp [Coordinates.equiv_apply, Coordinates.params, Coordinates.entry,
      coefficientSemilinearEquiv, coefficientEndomorphism, hb, mapCoefficients]
/-- Frobenius is the actual coefficient automorphism of the octonion group. -/
def frobeniusAutomorphism [Finite F] (k : ℕ) : MulAut (Model F) :=
  fieldEquiv (iterateFrobeniusEquiv F 2 k)
/-- Coefficient Frobenius and group Frobenius give identical twisted actions. -/
theorem frobeniusConjugate_eq [Finite F] (k : ℕ) :
    Representation.semilinearConjugate (V := Space F) (W := Space F) (iterateFrobeniusEquiv F 2 k) (action F)
      (coefficientSemilinearEquiv F (iterateFrobeniusEquiv F 2 k)) =
    (action F).comp (frobeniusAutomorphism F k).toMonoidHom :=
  coefficientConjugate_eq F _
/-- Frobenius compatibility as a genuine intertwining equivalence. -/
def frobeniusConjugateEquiv [Finite F] (k : ℕ) :
    Representation.RepEquiv
      (Representation.semilinearConjugate (V := Space F) (W := Space F)
        (iterateFrobeniusEquiv F 2 k) (action F)
        (coefficientSemilinearEquiv F (iterateFrobeniusEquiv F 2 k)))
      ((action F).comp (frobeniusAutomorphism F k).toMonoidHom) :=
  coefficientConjugateEquiv F _

/-- The Frobenius intertwiner is retained over every extension field. -/
def frobeniusConjugateEquiv_extendScalars [Finite F]
    (K : Type*) [Field K] [Algebra F K] (k : ℕ) :
    Representation.RepEquiv
      (Representation.extendScalars (F := F) (V := Space F) K
        (Representation.semilinearConjugate (V := Space F) (W := Space F)
          (iterateFrobeniusEquiv F 2 k) (action F)
          (coefficientSemilinearEquiv F (iterateFrobeniusEquiv F 2 k))))
      (Representation.extendScalars (F := F) (V := Space F) K
        ((action F).comp (frobeniusAutomorphism F k).toMonoidHom)) :=
  coefficientConjugateEquiv_extendScalars F K _
end CharacteristicTwo
end Atlas.G2.Restricted.Adjoint
