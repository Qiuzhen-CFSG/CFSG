module

public import Theory.Representation.BinaryOffender.QuasisimpleNormalizer

/-!
# The faithful component in an offender supplement

For a faithful linear action, adjoining normalizing operators preserves the
component as an isomorphic subgroup. Restricting to an intermediate actor
containing it preserves both this isomorphism and every action operator.
This is the elementary transport used before B.5.1 in source 3.2.8.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
variable {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) P W)

/-- The faithful component projection is an isomorphism. -/
def supplementComponentEquiv (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) : P ≃* component σ A :=
  MulEquiv.ofBijective (projection σ A)
    ⟨fun _ _ he => hf (congrArg (fun k : component σ A =>
      linearAction (supplement σ A) k) he), projection_surjective σ A⟩

/-- Restriction to a containing actor retains the same component. -/
def supplementActorEquiv (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) (J : Subgroup (supplement σ A))
    (hle : component σ A ≤ J) : P ≃* (component σ A).subgroupOf J :=
  (supplementComponentEquiv σ hf A).trans (subgroupOfEquivOfLe hle).symm

/-- This component identification preserves the literal linear operators. -/
theorem supplementActorEquiv_action (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) (J : Subgroup (supplement σ A))
    (hle : component σ A ≤ J) (p : P) :
    (linearAction (supplement σ A)).comp J.subtype
      (supplementActorEquiv σ hf A J hle p) = σ p := by
  ext v
  rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
