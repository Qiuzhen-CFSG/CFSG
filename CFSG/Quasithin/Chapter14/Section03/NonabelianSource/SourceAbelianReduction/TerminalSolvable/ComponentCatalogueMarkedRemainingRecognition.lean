module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedLowRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.Complete

/-!
# Marked image assembly after complete higher-multiplicity recognition

The low-displacement and higher-multiplicity branches now supply the actual
image cases. In particular the latter retains the normal A₇ row; it does
not need the stronger small-component output in the older conditional
assembly. The only remaining recognition inputs are faithful actors and
fixed-line two-copy actions, with the exact kernel and quotient dimensions
already discharged from the original marked source.

These two callbacks remain proof obligations of the marked-image owner.
Source: Aschbacher--Smith G.11.7--9, printed pp.366--369;14.3.15,p.994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
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

/-- All remaining source cases are reduced to faithful and fixed-line
 two-copy recognition; higher multiplicity is supplied unconditionally. -/
theorem imageCases_of_faithful_and_two_copy_recognition
    (hfaithful : ActorFaithful (F := F) (g := g) (I := I) →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases)
    (htwo : ¬ ActorFaithful (F := F) (g := g) (I := I) →
      finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I →
      Nat.card ((centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) = 2 →
      finrank (ZMod 2) I =
        finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
          (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
            (F.terminalDot (F.X g)))) + 2 →
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} → s.ImageCases) : s.ImageCases := by
  by_cases hf : ActorFaithful (F := F) (g := g) (I := I)
  · exact hfaithful hf s.fixedPointAlternative
  · by_cases hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v}
    · rcases s.constituent_dimension_cases_of_not_actorFaithful hf with hd | hd
      · exact htwo hf hd (s.actor_kernel_card_two_of_double_dimension hf hd)
          (s.actor_quotient_dimension_of_double_dimension hf hd) hfix
      · exact s.imageCases_of_higher_dimension hf hd
    · exact s.imageCases_of_smallComponentImage
        (s.smallComponentImage_of_not_actorFaithful_of_fixedSpace_ne_point hf hfix)

/-- The two genuine remaining recognition inputs suffice for the original
local lift, with no higher-multiplicity or low-displacement callback. -/
theorem local_lift_of_faithful_and_two_copy_recognition
    (hfaithful : ActorFaithful (F := F) (g := g) (I := I) →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases)
    (htwo : ¬ ActorFaithful (F := F) (g := g) (I := I) →
      finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I →
      Nat.card ((centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) = 2 →
      finrank (ZMod 2) I =
        finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
          (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
            (F.terminalDot (F.X g)))) + 2 →
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} → s.ImageCases) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_faithful_and_two_copy_recognition hfaithful htwo)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
