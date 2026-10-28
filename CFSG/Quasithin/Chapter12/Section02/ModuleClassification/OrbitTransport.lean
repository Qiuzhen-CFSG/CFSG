module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NormalizerTransport
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource

/-!
# Full-normalizer FF transport when the source seed is invariant

A genuine source orbit equality gives equality of the original subspaces
inside the reduced module. The restricted component action and its full
normalizer therefore agree with those of the seed. This transport is used
only after the source equality has been supplied.
Source: Aschbacher--Smith 3.2.5 and 12.2.2, pp.580,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

private theorem normalizer_ff_congr {A E : Type*} [Group A]
    [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (X : Subgroup A)
    {I J : Submodule (ZMod 2) E} (he : I = J) :
    IsFFModule (normalizerRepresentation
      ((subspaceImageRepresentation ρ I).comp (restrictedSubgroup ρ I X).subtype)) ↔
    IsFFModule (normalizerRepresentation
      ((subspaceImageRepresentation ρ J).comp (restrictedSubgroup ρ J X).subtype)) := by
  subst I
  rfl

theorem chosen_normalizer_ff_iff_orbit_of_eq
    (hVW : V = D.sourceOrbit) :
    IsFFModule (normalizerRepresentation D.chosenAction) ↔
      IsFFModule D.sourceOrbitNormalizerRepresentation := by
  have he : D.orbitSpace = D.space := ReducedNormal.subspaceImage_injective
    (L ⊔ (T : Subgroup G)) (hVW.symm.trans D.image_eq.symm)
  exact D.chosen_normalizer_ff_iff_seedComponent.trans
    (normalizer_ff_congr (reducedRepresentation (L ⊔ (T : Subgroup G)))
      (L.subgroupOf (L ⊔ (T : Subgroup G))) he).symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
