module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.Action

/-!
# Assembly of actual D4 normalizer and opposite-root lifts

The normalizer comparison gives a homomorphism on the actual torus normalizer.
Its descended action agrees with the supplied `TorusData` by the simple-root
character equations. Faithfulness then identifies the Weyl image of each
representative constructed in the two opposite root groups.

This is conditional assembly: the normalizer realization and the opposite-root
representatives remain geometric inputs. The whole-torus centralizer bound is
handled separately by `LiftAction.toRealization` in `Normalizer.Inputs`.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 6.1--6.4, 8.2(4)--(5),
and 8.3(c); GLS3, Chapter 1, Theorem 1.9.5(f).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup
namespace ConnectedCentralizer.Normalizer
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Combine the actual normalizer comparison with opposite-root representatives.
Faithfulness identifies their Weyl images; neither geometric input is asserted
here to exist without its own proof. -/
def liftAction_of_normalizerRealization_of_oppositeReflectionLifts
    (S : Geometry K) {n : ℕ} (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (hroot : OppositeReflectionLifts S D) : LiftAction S D where
  toWeyl := R.toWeyl
  conjugation := normalizer_conjugation S D R
  reflection_lift := by
    let := D.action
    intro a
    obtain ⟨g, hg, hconj⟩ := hroot a
    refine ⟨g, ?_, hg⟩
    apply weyl_eq_of_smul S D
    intro t
    apply S.torus.inclusion_injective
    exact (normalizer_conjugation S D R g t).trans (hconj t).symm

/-- Existential form of the conditional assembly. Both premises must be
constructed before this gives unconditional existence of `LiftAction`. -/
theorem nonempty_liftAction_of_normalizerRealization_of_oppositeReflectionLifts
    (S : Geometry K) {n : ℕ} (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (hroot : OppositeReflectionLifts S D) : Nonempty (LiftAction S D) :=
  ⟨liftAction_of_normalizerRealization_of_oppositeReflectionLifts S D R hroot⟩

end ConnectedCentralizer.Normalizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
