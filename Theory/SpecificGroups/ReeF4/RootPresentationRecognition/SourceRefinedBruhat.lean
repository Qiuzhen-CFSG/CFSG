module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.RefinedBruhat
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceFaithfulness
/-!
# Unique refined coordinates on the same marked source quotient

Evaluate the abstract restricted normal form on the actual source charts,
full torus and Weyl lifts. The independently proved source kernel gives a
bijection, retaining the native inversion-root restriction on the right tuple.
Source: GLS3 2.3.5--8; Steinberg section 11, Theorem 33 and Lemma 62.
The source construction and verification of the finite equations remain explicit.
-/

@[expose] public noncomputable section

namespace ReeF4.RootPresentationRecognition.Global
open Subgroup Theory.GroupTheory OrderedRootPresentation
open CentralCovers.TwoPrimary CentralCovers.OddPrimary.Order
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)
variable (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)
variable (E : SourceAngular.Equations Q split d)
variable (R : SourceSigned.Equations Q split d T W) (A : SourceGauss Q split d T W)

/-- The same restricted tuples evaluated on the literal original source charts,
full two-unit torus and Weyl lifts, rather than a new quotient or model tag. -/
def sourceRefinedWord (z : RefinedParameters m) : X ⧸ Q.D :=
  word (AngularPresentation.Parameter m) (fun i => SourceAngular.sourceRoot Q split d i) sourceOrder z.2.1 *
    T.h z.2.2.1 * SourceSigned.weyl Q split d T W z.1 *
      word (AngularPresentation.Parameter m) (fun i => SourceAngular.sourceRoot Q split d i) sourceOrder z.2.2.2.val

theorem sourceEval_refinedWord (z : RefinedParameters m) :
    sourceEval Q split d T W E R A (refinedWord m z) = sourceRefinedWord Q split d T W z := by
  have hp (p : PositiveParameters m) : sourceEval Q split d T W E R A (positiveWord m p) =
      word (AngularPresentation.Parameter m) (fun i => SourceAngular.sourceRoot Q split d i) sourceOrder p := by
    rw [positiveWord,map_word]
    congr 1
    funext i a
    exact Presentation.eval_root (source Q split d T W) (source_relations Q split d T W E R A) true i a
  simp only [refinedWord,map_mul,hp,sourceEval_torus,sourceEval_weyl]
  change _ * T.h ((fixedTorusEquiv m).symm (fixedTorusEquiv m z.2.2.1)) * _ * _ = _
  rw [MulEquiv.symm_apply_apply]
  rfl

include E R A in
/-- Both whole-group kernels and refined native uniqueness yield unique source
coordinates without assuming any source normal-form or faithfulness callback. -/
theorem sourceRefinedWord_bijective : Function.Bijective (sourceRefinedWord Q split d T W) := by
  have he : sourceRefinedWord Q split d T W =
      (sourceEval Q split d T W E R A) ∘ refinedWord m := by
    funext z
    exact (sourceEval_refinedWord Q split d T W E R A z).symm
  rw [he]
  exact (sourceEquiv Q split d T W E R A).bijective.comp
    ⟨refinedWord_injective m,refinedWord_surjective m⟩

end ReeF4.RootPresentationRecognition.Global
