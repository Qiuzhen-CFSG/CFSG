module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NormalizerTransport
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FFSource

/-!
# The seed offender in the original full normalizer

The faithful seed actor embeds in the full linear normalizer of its normal
component image. The same offender therefore acts on the same chosen vectors
in the original full-normalizer FF hypothesis.
Source: Aschbacher--Smith B.1.11--13 and 12.2.2, pp.72--73,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

theorem chosen_normalizer_ff_of_seed (hseed : IsFFModule D.seedRepresentation) :
    IsFFModule (normalizerRepresentation D.chosenAction) := by
  have hf : Function.Injective (actionHom D.seedRepresentation) := by
    intro x y hxy
    exact subspaceImageRepresentation_injective _ _
      (congrArg (imageRepresentation D.seedRepresentation) hxy)
  have himage := hseed.map_equivariant D.seedRepresentation (imageRepresentation D.seedRepresentation)
    (actionHom D.seedRepresentation) hf
    (LinearEquiv.refl _ _) (fun _ _ => rfl)
  exact D.chosen_normalizer_ff_iff_seedComponent.mpr
    (isFFModule_linearNormalizer D.seedRepresentation D.componentImage himage)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
