module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedTwoCopyComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedRemainingRecognition

/-!
# Complete nonfaithful marked recognition and faithful-only final assembly

The complete two-copy and higher-multiplicity classifiers cover every
nonfaithful original actor. The actual image and intrinsic local lift are
therefore reduced to the single remaining faithful-actor source branch.
The faithful premise below remains explicit and must be discharged by this
marked-image owner; no full classification is asserted here.
Source: Aschbacher–Smith G.11.7–9 and 14.3.15, printed pp.366–369,994.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

open scoped MatrixGroups
open Chapter1.Section02.LocalModels

/-- Every nonfaithful marked actor has the original full image cases. -/
theorem imageCases_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) : s.ImageCases := by
  rcases s.constituent_dimension_cases_of_not_actorFaithful hk with hd | hd
  · exact s.imageCases_of_double_dimension_complete hk hd
  · exact s.imageCases_of_higher_dimension hk hd

/-- The complete nonfaithful branch supplies the actual intrinsic local lift. -/
theorem local_lift_of_not_actorFaithful
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_not_actorFaithful hk)

/-- Only the original faithful-actor recognition obligation remains. -/
theorem imageCases_of_faithful_recognition
    (hfaithful : ActorFaithful (F := F) (g := g) (I := I) →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases) : s.ImageCases := by
  by_cases hf : ActorFaithful (F := F) (g := g) (I := I)
  · exact hfaithful hf s.fixedPointAlternative
  · exact s.imageCases_of_not_actorFaithful hf

/-- Faithful recognition alone now suffices for the original local lift. -/
theorem local_lift_of_faithful_recognition
    (hfaithful : ActorFaithful (F := F) (g := g) (I := I) →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_faithful_recognition hfaithful)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
