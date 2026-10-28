module

public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.Representation.SemilinearConjugation
public import Mathlib.FieldTheory.Perfect

/-!
# Coefficient automorphisms of the natural G₂ module

The six-coordinate action is obtained from integral octonion multiplication.
Conjugating its coefficients by any field automorphism therefore equals
precomposition with the actual automorphism `Atlas.G2.fieldEquiv` of G₂.
In particular this identifies coefficient Frobenius twists as representations,
not just by dimension or character.

Source: GLS3, Definition 2.8.3 and Remark 2.8.8.
-/

@[expose] public noncomputable section

namespace Atlas.G2.Restricted.NaturalCoordinates

open Atlas.SplitOctonion

variable (F : Type*) [Field F] [CharP F 2]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Field transport on six coordinates intertwines the actual field automorphism. -/
theorem action_fieldEquiv (e : F ≃+* F) (g : Model F) (v : Space F) :
    action F (fieldEquiv e g) (fun i => e (v i)) =
      fun i => e (action F g v i) := by
  have hrep : mapCoefficients e (representative F v).val =
      (representative F (fun i => e (v i))).val := by
    ext i
    fin_cases i <;> simp [mapCoefficients, representative]
  have h := fieldEquiv_action e g (representative F v).val
  rw [hrep] at h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 5
  · exact congrFun h 6
  · exact congrFun h 7

/-- Equality of the coefficient-conjugate and group-automorphism-twisted actions. -/
theorem coefficientConjugate_eq (e : F ≃+* F) :
    Representation.semilinearConjugate e (action F)
        (Representation.coordinateSemilinearEquiv e (Fin 6)) =
      (action F).comp (fieldEquiv e).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  have h := action_fieldEquiv F e g (fun j => e.symm (v j))
  have hv : (fun j => e (e.symm (v j))) = v := by
    funext j
    exact e.apply_symm_apply (v j)
  rw [hv] at h
  simp only [Representation.semilinearConjugate_apply,
    Representation.coordinateSemilinearEquiv_apply]
  have hinv : (Representation.coordinateSemilinearEquiv e (Fin 6)).symm v =
      fun j => e.symm (v j) := by
    funext j
    exact Representation.coordinateSemilinearEquiv_symm_apply e (Fin 6) v j
  rw [hinv]
  exact (congrFun h i).symm

/-- A genuine intertwining equivalence for coefficient conjugation. -/
def coefficientConjugateEquiv (e : F ≃+* F) :
    Representation.RepEquiv
      (Representation.semilinearConjugate e (action F)
        (Representation.coordinateSemilinearEquiv e (Fin 6)))
      ((action F).comp (fieldEquiv e).toMonoidHom) where
  toLinearEquiv := LinearEquiv.refl F _
  isIntertwining' g := by
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    exact DFunLike.congr_fun (coefficientConjugate_eq F e) g

/-- The field Frobenius on the actual G₂ model over a finite field. -/
def frobeniusAutomorphism [Finite F] (r : ℕ) : MulAut (Model F) :=
  fieldEquiv (iterateFrobeniusEquiv F 2 r)

/-- Coefficient Frobenius is twisting by the genuine group automorphism. -/
theorem frobeniusConjugate_eq [Finite F] (r : ℕ) :
    Representation.semilinearConjugate (iterateFrobeniusEquiv F 2 r) (action F)
        (Representation.coordinateSemilinearEquiv (iterateFrobeniusEquiv F 2 r) (Fin 6)) =
      (action F).comp (frobeniusAutomorphism F r).toMonoidHom :=
  coefficientConjugate_eq F _

end Atlas.G2.Restricted.NaturalCoordinates
