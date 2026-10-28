module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulGeometry
public import CFSG.Quasithin.ChapterG.Section09.QuasiequivalenceSymmetry

/-!
# Selecting a moved component for the faithful exchanged action

The literal stabilizer has order 2^(dim I - 2), hence is nontrivial. Its
faithful conjugation action on the normal component orbit moves at least
one component. If it centralizes the originally selected component, the
partner is moved and its ordinary or dual comparison is reversed. This
supplies G.9.3 on the same faithful orbit image, without asserting movement
of a particular component. Recognition of that image remains the separate
model-sieve obligation, and transports back to the original component.

Source: Aschbacher--Smith G.11.6, printed p.366, applying G.9.3.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s

/-- The nontrivial stabilizer acts nontrivially on the whole component orbit. -/
theorem orbit_actor_moved :
    ⁅componentOrbit L ⊤, actor (F := F) (g := g) (I := I)⁆ ≠ ⊥ := by
  intro hz
  let A := actor (F := F) (g := g) (I := I)
  let X := F.terminalDot (F.X g)
  let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf X
  have hAC : A ≤ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have htriv : ∀ a : A, a = 1 := by
    intro a
    have hh := s.completion.2.2.2 (⟨⟨a,a.property.2⟩,a.property.1⟩ : Y)
      (hAC a.property)
    apply Subtype.ext
    exact congrArg (fun y : Y => ((y : X) : F.TerminalHdot)) hh
  have hc : Nat.card A = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,htriv⟩
  have hd := s.dimension_gt_two
  have hp := one_lt_pow' (show (1 : ℕ) < 2 by decide)
    (show finrank (ZMod 2) I - 2 ≠ 0 by omega)
  rw [← s.actor_card] at hp
  change 1 < Nat.card A at hp
  omega

/-- Some actual component of the same faithful orbit image satisfies G.9.3.
If the original component is centralized, select its partner and reverse
its ordinary or dual comparison. The orbit group itself never changes. -/
theorem exists_image_component_hypothesis :
    ∃ C : Subgroup s.actionQuotient,
      C ≤ s.image (componentOrbit L ⊤) ∧
      ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple s.imageAction
        (s.image (actor (F := F) (g := g) (I := I))) C
        (s.image (componentOrbit L ⊤)) (finrank (ZMod 2) I - 2) := by
  classical
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  let : IsElementaryAbelian 2 (actor (F := F) (g := g) (I := I)) := actor_elementary
  have himage {C : Subgroup F.TerminalHdot} (hC : C ≤ componentOrbit L ⊤) :
      s.image C ≤ s.image (componentOrbit L ⊤) :=
    Subgroup.map_mono (fun _ hx => hC hx)
  by_cases hm : ⁅L,actor (F := F) (g := g) (I := I)⁆ ≠ ⊥
  · exact ⟨s.image L,himage (le_componentOrbit L ⊤),s.componentInput_of_actor_moved hm⟩
  have hz : ⁅L,actor (F := F) (g := g) (I := I)⁆ = ⊥ := not_ne_iff.mp hm
  rcases s.constituent_components with he | ⟨L₂,h₂H,h₂,he,hq⟩
  · exact False.elim (s.orbit_actor_moved (by rw [he]; exact hz))
  have hm₂ : ⁅L₂,actor (F := F) (g := g) (I := I)⁆ ≠ ⊥ := by
    intro hz₂
    apply s.orbit_actor_moved
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [he]
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hz)
      (commutator_eq_bot_iff_le_centralizer.mp hz₂)
  refine ⟨s.image L₂,himage h₂H,?_⟩
  apply ChapterG.Section09.componentHypothesis_constituent_or_dual
    F.terminalRepresentation ⟨Recognition.terminal_sqtkCover s.simple F (by decide)⟩
    (actor (F := F) (g := g) (I := I)) L₂ (componentOrbit L ⊤) I
    s.selected.invariant inf_le_left s.orbit_faithful s.actor_faithful s.irreducible
    (finrank (ZMod 2) I - 2) s.actor_card s.image_setup.degree_le
    h₂ hm₂ h₂H
  refine Or.inr ⟨L,le_componentOrbit L ⊤,s.component,he.trans (sup_comm _ _),?_⟩
  rcases hq with hq | hq
  · exact Or.inl (ChapterG.Section09.quasiequivalent_symm _ _ hq)
  · exact Or.inr (ChapterG.Section09.quasiequivalent_dual_symm _ _ hq)

/-- The remaining model sieve belongs to the exchanged-image recognition
owner. Recognizing H from any genuine moved component still recognizes the
original component L through the already proved orbit transport. -/
theorem componentImageCases_of_moved_image_recognition
    (recognize : ∀ C : Subgroup s.actionQuotient,
      C ≤ s.image (componentOrbit L ⊤) →
      ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple s.imageAction
        (s.image (actor (F := F) (g := g) (I := I))) C
        (s.image (componentOrbit L ⊤)) (finrank (ZMod 2) I - 2) →
      Nonempty (s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 7))) :
    ComponentImageCases L := by
  obtain ⟨C,hCH,hC⟩ := s.exists_image_component_hypothesis
  obtain ⟨e⟩ := recognize C hCH hC
  exact s.componentImageCases_of_image_alternating_seven e

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
