module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpGeometry
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SourceModels

/-!
# Original marked consumers of the triality, Ree and Tits exclusions

The genuine component input excludes the three actual twisted rank-two
carriers at the original G.9 degree bound. The following consumers preserve
the literal action and its marked component. Two-copy and proper faithful
geometry discharge equality with the component orbit. The whole-space
faithful route explicitly retains that equality.

Source: Aschbacher–Smith G.11.7–8 and 14.3.15, printed pp.366–369,994.
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
  {k : Type*} [Field k] [Finite k]
include s

/-- The three actual twisted rank-two rows cannot occur in the two-copy action. -/
theorem not_double_dimension_triality_ree_tits
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (model : (∃ n : ℕ, 0 < n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n)
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ Chapter1.Section02.LocalModels.IsReeF4At
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) k) ∨
      Nonempty ((MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) ≃* Tits.ParrottGroup)) : False := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_double_dimension hk hd
  dsimp only at hc
  rw [he] at hc
  rcases model with ⟨n, hn, model⟩ | ⟨k, hk, d, ⟨e⟩⟩ | e
  · exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_triality_positive_exponent
      hc hn model
  · exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_ree_of_local_block
      hc hk d e
  · exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_tits_of_source_component
      hc e.some

/-- The faithful single-orbit action uses the original degree bound. -/
theorem not_faithful_single_orbit_triality_ree_tits
    (hf : ActorFaithful (F := F) (g := g) (I := I)) (hHL : componentOrbit L ⊤ = L)
    (model : (∃ n : ℕ, 0 < n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n)
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ Chapter1.Section02.LocalModels.IsReeF4At
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) k) ∨
      Nonempty ((MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) ≃* Tits.ParrottGroup)) : False := by
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_actorFaithful hf
  dsimp only at hc
  rw [he] at hc
  rcases model with ⟨n, hn, model⟩ | ⟨k, hk, d, ⟨e⟩⟩ | e
  · exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_triality_positive_exponent
      hc hn model
  · exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_ree_of_local_block
      hc hk d e
  · exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_tits_of_source_component
      hc e.some

/-- The two-copy exclusions feed the original intrinsic local lift. -/
theorem local_lift_of_double_dimension_triality_ree_tits
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (model : (∃ n : ℕ, 0 < n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n)
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ Chapter1.Section02.LocalModels.IsReeF4At
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) k) ∨
      Nonempty ((MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) ≃* Tits.ParrottGroup)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_double_dimension_triality_ree_tits hk hd model).elim

/-- Proper faithful geometry supplies orbit equality for the original local lift. -/
theorem local_lift_of_faithful_triality_ree_tits
    (hf : ActorFaithful (F := F) (g := g) (I := I))
    (hgeometry : I ≠ ⊤ ∨ componentOrbit L ⊤ = L)
    (model : (∃ n : ℕ, 0 < n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n)
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ Chapter1.Section02.LocalModels.IsReeF4At
        (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) k) ∨
      Nonempty ((MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) ≃* Tits.ParrottGroup)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  have hHL : componentOrbit L ⊤ = L := hgeometry.elim
    (s.orbit_eq_component_of_actorFaithful_of_ne_top hf) id
  exact (s.not_faithful_single_orbit_triality_ree_tits hf hHL model).elim
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
