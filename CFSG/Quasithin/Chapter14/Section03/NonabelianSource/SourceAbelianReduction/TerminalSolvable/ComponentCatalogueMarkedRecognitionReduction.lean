module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelTwoCopies
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.Reduction

/-!
# Original local lift after the marked geometric reductions

The same-vector fixed-point alternative, the exact two-copy kernel and its
rank loss, and the higher-multiplicity fixed line are all supplied by their
source proofs. The faithful and two nonfaithful recognition branches remain
explicit hypotheses. Their resulting literal image cases feed the original
local lift and intrinsic two-core quotient, including the ambient-normality
conditions carried by the faithful large rows.

Source: Aschbacher--Smith G.11.6--9 and 14.3.15, printed pp.366--369,994.
This is conditional assembly, not an unconditional component catalogue.
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

/-- Small component recognition transports through the actual faithful orbit
map, without any ambient-normality condition in these two rows. -/
theorem imageCases_of_smallComponentImage (hc : SmallComponentImage L) : s.ImageCases := by
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let e := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  rcases hc with h5 | h6
  · exact Or.inr (Or.inl (Or.inl (h5.map e.symm.trans)))
  · exact Or.inr (Or.inl (Or.inr (h6.map e.symm.trans)))

/-- All selected-vector and multiplicity premises are discharged before
the remaining image-recognition arguments reach the original local lift.

The three recognition hypotheses are explicit unfinished source branches.
This theorem does not assert their model classification. Final catalogue
assembly remains with qt-e-14315-terminal-solvable; their proofs and this
marked-image assembly remain with qt-e-14315-component-marked-images. -/
theorem local_lift_of_marked_recognition
    (hfaithful : ActorFaithful (F := F) (g := g) (I := I) →
      FixedPointAlternative (F := F) (g := g) (v := v) → s.ImageCases)
    (htwo : ¬ ActorFaithful (F := F) (g := g) (I := I) →
      Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I →
      Nat.card ((centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) = 2 →
      Module.finrank (ZMod 2) I =
        Module.finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
          (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
            (F.terminalDot (F.X g)))) + 2 →
      (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
          Submodule.span (ZMod 2) {v} ∨
        ∃ a : F.terminalDot (F.X g), a ≠ 1 ∧
          (a : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) ∧
          Module.finrank (ZMod 2)
            (LinearMap.range ((F.terminalRepresentation a - 1).comp I.subtype)) = 1) →
      SmallComponentImage L)
    (hhigher : ¬ ActorFaithful (F := F) (g := g) (I := I) →
      2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat) →
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} → SmallComponentImage L) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  apply s.local_lift_of_image_cases
  by_cases hf : ActorFaithful (F := F) (g := g) (I := I)
  · exact hfaithful hf s.fixedPointAlternative
  · apply s.imageCases_of_smallComponentImage
    rcases s.constituent_dimension_cases_of_not_actorFaithful hf with hd | hd
    · exact htwo hf hd (s.actor_kernel_card_two_of_double_dimension hf hd)
        (s.actor_quotient_dimension_of_double_dimension hf hd)
        (s.fixedPoint_or_constituent_transvection hf hd)
    · exact hhigher hf hd (s.source_fixedSpace_eq_point_of_higher_dimension hd)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
