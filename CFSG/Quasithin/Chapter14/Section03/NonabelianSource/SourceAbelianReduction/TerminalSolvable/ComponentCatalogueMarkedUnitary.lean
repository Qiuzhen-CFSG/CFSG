module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpGeometry
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.UnitarySource

/-!
# Original marked consumers of the unitary exclusion

The genuine component input excludes both SU3 and PSU3 for every positive
binary exponent, on the actual constituent image. Two-copy and proper
faithful geometry discharge equality with the normal orbit. Whole-space
faithful applications explicitly retain that equality; they do not acquire
the stronger sharp constituent bound. Both routes feed the original local lift.

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

open BenderSuzuki.MatrixGroups
/-- The original two-copy action cannot have either unitary model. -/
theorem not_double_dimension_unitary_three
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (J : HermitianForm 3 k) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card k = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (model : Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃* J.specialSubgroup) ∨
      Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        ProjectiveSpecialUnitaryMatrixGroup J)) : False := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_double_dimension hk hd
  dsimp only at hc
  rw [he] at hc
  exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_unitary_three_positive_exponent
    hc J hn hcard hconj model

/-- The faithful single-orbit action is excluded at the original G.9 bound. -/
theorem not_faithful_single_orbit_unitary_three
    (hf : ActorFaithful (F := F) (g := g) (I := I)) (hHL : componentOrbit L ⊤ = L)
    (J : HermitianForm 3 k) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card k = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (model : Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃* J.specialSubgroup) ∨
      Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        ProjectiveSpecialUnitaryMatrixGroup J)) : False := by
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_actorFaithful hf
  dsimp only at hc
  rw [he] at hc
  exact ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.not_unitary_three_positive_exponent
    hc J hn hcard hconj model

/-- The two-copy exclusion supplies the actual intrinsic local lift. -/
theorem local_lift_of_double_dimension_unitary_three
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (J : HermitianForm 3 k) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card k = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (model : Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃* J.specialSubgroup) ∨
      Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_double_dimension_unitary_three hk hd J n hn hcard hconj model).elim

/-- A proper faithful constituent supplies its orbit equality automatically. -/
theorem local_lift_of_faithful_unitary_three
    (hf : ActorFaithful (F := F) (g := g) (I := I))
    (hgeometry : I ≠ ⊤ ∨ componentOrbit L ⊤ = L)
    (J : HermitianForm 3 k) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card k = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (model : Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃* J.specialSubgroup) ∨
      Nonempty (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  have hHL : componentOrbit L ⊤ = L := hgeometry.elim
    (s.orbit_eq_component_of_actorFaithful_of_ne_top hf) id
  exact (s.not_faithful_single_orbit_unitary_three hf hHL J n hn hcard hconj model).elim
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
