module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.HighestVector

/-!
# Detecting zero highest weights in the actual G₂ tensor actions

The short and long Weyl reflections fix the highest vector exactly when the
corresponding binary weight is zero. An explicit coefficient is one on the
highest vector and zero on its reflected image whenever that weight is positive.
This distinguishes zero from the boundary weight q−1, even though they have the
same character on the finite split torus.

Together with highest-line uniqueness and the coroot characters, this is the
extra action information needed for distinctness in GLS3, 2.8.6(a), 2.8.9 and
2.8.10(g). All formulas use the actual octonion-group action.

The concrete coordinate actions use the attributed ATLAS port already imported
by `RestrictedModules`; see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Atlas.G2.TensorClassification
open Restricted
variable (F : Type*) [Field F] [CharP F 2]

/-- The short and long simple Weyl reflections in Wilson's coordinates. -/
def simpleReflection (s : Bool) : Model F := if s then weylR else weylS

omit [CharP F 2] in
private theorem field_simpleReflection (σ : F ≃+* F) (s : Bool) :
    fieldEquiv σ (simpleReflection F s) = simpleReflection F s := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  cases s <;> fin_cases i <;>
    simp [simpleReflection, fieldEquiv, Atlas.SplitOctonion.transportAutomorphism,
      Atlas.SplitOctonion.transportLinear, Atlas.SplitOctonion.mapCoefficients,
      weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply]

/-- The actual reflected highest vector has coefficient zero for a nonzero bit. -/
theorem factorHighestCoefficient_reflection (a : Factor) (s : Bool) :
    factorHighestCoefficient F a
      (action F a (simpleReflection F s) (highestVector F a)) =
        if weightBit s a = 0 then 1 else 0 := by
  cases s <;> cases a
  · rfl
  · change (NaturalCoordinates.action F weylS (NaturalCoordinates.highestVector F)) 0 = 0
    simp [NaturalCoordinates.highestVector]
  · change Adjoint.Coordinates.equiv F
      (Adjoint.action F weylS (Adjoint.highestVector F)) 0 = 1
    rw [Adjoint.equiv_action, Adjoint.equiv_highestVector]
    simp [Adjoint.Coordinates.highestVector]
  · change Steinberg.coordinates F
      (Steinberg.ambientAction F weylS (Steinberg.seed F)) (0, 0, 1) = 0
    simp [Steinberg.seed, Steinberg.e]
  · rfl
  · change (NaturalCoordinates.action F weylR (NaturalCoordinates.highestVector F)) 0 = 1
    simp [NaturalCoordinates.highestVector]
  · change Adjoint.Coordinates.equiv F
      (Adjoint.action F weylR (Adjoint.highestVector F)) 0 = 0
    rw [Adjoint.equiv_action, Adjoint.equiv_highestVector]
    simp [Adjoint.Coordinates.highestVector]
  · change Steinberg.coordinates F
      (Steinberg.ambientAction F weylR (Steinberg.seed F)) (0, 0, 1) = 0
    simp [Steinberg.seed, Steinberg.e]

/-- A vanishing restricted coroot coordinate means that its reflection fixes the vector. -/
theorem factorHighestVector_reflection_of_weight_eq_zero (a : Factor) (s : Bool)
    (h : weightBit s a = 0) :
    action F a (simpleReflection F s) (highestVector F a) = highestVector F a := by
  cases s <;> cases a
  · rfl
  · contradiction
  · change Adjoint.action F weylS (Adjoint.highestVector F) = Adjoint.highestVector F
    apply (Adjoint.Coordinates.equiv F).injective
    rw [Adjoint.equiv_action, Adjoint.equiv_highestVector]
    ext i
    fin_cases i <;> simp [Adjoint.Coordinates.highestVector]
  · contradiction
  · rfl
  · change NaturalCoordinates.action F weylR (NaturalCoordinates.highestVector F) =
      NaturalCoordinates.highestVector F
    ext i
    fin_cases i <;> simp [NaturalCoordinates.highestVector]
  · contradiction
  · contradiction

variable [Finite F]

theorem factorRep_simpleReflection (r : ℕ) (a : Factor) (s : Bool) :
    factorRep F r a (simpleReflection F s) = action F a (simpleReflection F s) := by
  change action F a (fieldEquiv (iterateFrobeniusEquiv F 2 r) _) = _
  rw [field_simpleReflection]

theorem wordHighestCoefficient_reflection (r : ℕ) (w : List Factor) (s : Bool) :
    wordHighestCoefficient F w (wordRep F r w (simpleReflection F s) (wordHighestVector F w)) =
      if wordWeight s w = 0 then 1 else 0 := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
    change (TensorProduct.lid F F)
      (TensorProduct.map (factorHighestCoefficient F a) (wordHighestCoefficient F w)
        (factorRep F r a (simpleReflection F s) (highestVector F a) ⊗ₜ[F]
          wordRep F (r + 1) w (simpleReflection F s) (wordHighestVector F w))) = _
    rw [TensorProduct.map_tmul, TensorProduct.lid_tmul, factorRep_simpleReflection,
      factorHighestCoefficient_reflection, ih]
    by_cases ha : weightBit s a = 0 <;> by_cases hw : wordWeight s w = 0 <;>
      simp [wordWeight, ha, hw]

theorem wordHighestVector_reflection_of_weight_eq_zero (r : ℕ) (w : List Factor)
    (s : Bool) (h : wordWeight s w = 0) :
    wordRep F r w (simpleReflection F s) (wordHighestVector F w) = wordHighestVector F w := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
    have ha : weightBit s a = 0 := by simp only [wordWeight] at h; omega
    have hw : wordWeight s w = 0 := by simp only [wordWeight] at h; omega
    change factorRep F r a (simpleReflection F s) (highestVector F a) ⊗ₜ[F]
      wordRep F (r + 1) w (simpleReflection F s) (wordHighestVector F w) = _
    rw [factorRep_simpleReflection, factorHighestVector_reflection_of_weight_eq_zero F a s ha,
      ih (r + 1) hw]
    rfl

variable (K : Type*) [Field K] [Algebra F K]

/-- Genuine Weyl action distinguishes weight zero from every positive weight,
including q−1. This remains valid after arbitrary extension of scalars. -/
theorem tensorHighestVector_reflection_iff {n : ℕ} (w : Fin n → Factor) (s : Bool) :
    tensorRep F K w (simpleReflection F s) (tensorHighestVector F K w) =
      tensorHighestVector F K w ↔ wordWeight s (List.ofFn w) = 0 := by
  constructor
  · intro h
    have hc := congrArg (tensorHighestCoefficient F K w) h
    rw [tensorHighestCoefficient_highestVector] at hc
    change (TensorProduct.AlgebraTensorModule.rid F K K)
      ((wordHighestCoefficient F (List.ofFn w)).baseChange K
        ((1 : K) ⊗ₜ[F] wordRep F 0 (List.ofFn w) (simpleReflection F s)
          (wordHighestVector F (List.ofFn w)))) = 1 at hc
    rw [LinearMap.baseChange_tmul, wordHighestCoefficient_reflection] at hc
    by_contra hw
    simp [hw] at hc
  · intro h
    change (1 : K) ⊗ₜ[F]
      wordRep F 0 (List.ofFn w) (simpleReflection F s) (wordHighestVector F (List.ofFn w)) = _
    rw [wordHighestVector_reflection_of_weight_eq_zero F 0 _ s h]
    rfl

end Atlas.G2.TensorClassification
end
