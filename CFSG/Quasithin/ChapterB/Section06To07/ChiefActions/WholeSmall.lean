module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallThompson
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallPair

/-!
# The whole small natural chief actions

The small solvable classification already records the full actor and natural
coordinates on its moved space. Equality of that space with the whole chief
module makes this a classification of the original action. The marked
single and paired five-point sections upgrade to actual action equivalences
on the whole module by their proved recognition theorems.

Source: Aschbacher–Smith, original 3.1.9(5) and 15.1.12(3).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

def ChiefSmallWholeAction (ρ : Representation (ZMod 2) D W) : Prop :=
  (SmallNaturalWreathAction ρ ∧ subspaceCommutator ρ ⊤ (offenderSubgroup ρ) = ⊤) ∨
    Nonempty (ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 5))) ∨
    Nonempty (ActionEquiv ρ BinaryPermutation.FivePair.wreathRepresentation)

variable [Finite D] [FiniteDimensional (ZMod 2) W]

theorem minimalParabolic_chief_small_whole_action
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hsmall : SmallNaturalWreathAction (imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (imageRepresentation ρ) ∨
      ChiefFivePairMarkedSection (imageRepresentation ρ))
    (hwhole : subspaceCommutator (imageRepresentation ρ) ⊤
      (offenderSubgroup (imageRepresentation ρ)) = ⊤) :
    ChiefSmallWholeAction (imageRepresentation ρ) := by
  rcases hsmall with hs | hs | hs
  · exact Or.inl ⟨hs,hwhole⟩
  · exact Or.inr (Or.inl (minimalParabolic_chief_five_of_marked ρ S hS hff hs).1)
  · obtain ⟨e,he⟩ := minimalParabolic_chief_five_pair_of_marked ρ S hS hff hs
    exact Or.inr (Or.inr ⟨e⟩)
end CFSG.Quasithin.ChapterB
