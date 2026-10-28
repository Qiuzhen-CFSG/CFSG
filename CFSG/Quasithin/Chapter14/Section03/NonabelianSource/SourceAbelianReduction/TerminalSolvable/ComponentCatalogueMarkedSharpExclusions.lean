module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpGeometry
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentSharpExclusions

/-!
# Sharp Mathieu and triple-A6 exclusions in the marked two-copy branch

The checked single-component geometry identifies the original component orbit.
The exact constituent image then satisfies G.9 with m = dim I−2, so the shared
sharp-degree exclusions apply without an added model or rank premise. Every
model below is an actual group or central-quotient isomorphism, and the final
theorem supplies the original intrinsic component lift.

Source: Aschbacher–Smith G.9.3 and G.11.8, printed pp.353–356,368–369;
14.3.15, printed p.994.
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

/-- None of these actual carrier rows occurs in the sharp two-copy action. -/
theorem not_double_dimension_mathieu_triple_six
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (model : let D : Type _ := ↥(MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)
      Nonempty (D ≃* Sporadic.Mathieu.M12) ∨ Nonempty (D ≃* Sporadic.Mathieu.M22) ∨
        Nonempty (D ≃* Sporadic.Mathieu.M23) ∨ Nonempty (D ≃* Sporadic.Mathieu.M24) ∨
        Nonempty ((D ⧸ center D) ≃* Sporadic.Mathieu.M22) ∨
        (Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 6)) ∧ Nat.card (center D) = 3)) : False := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_double_dimension hk hd
  dsimp only at hc
  rw [he] at hc
  have hsharp : Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) I - 2 + 2 := by
    have := s.dimension_gt_two
    omega
  rcases model with e | e | e | e | e | eh
  · exact hc.not_m12_of_sharp_degree hsharp e.some
  · exact hc.not_m22_of_sharp_degree hsharp e.some
  · exact hc.not_m23_of_sharp_degree hsharp e.some
  · exact hc.not_m24_of_sharp_degree hsharp e.some
  · exact hc.not_m22_central_quotient_of_sharp_degree hsharp e.some
  · exact hc.not_triple_alternating_six_of_sharp_degree hsharp eh.1.some eh.2

/-- Apply the excluded rows to the actual original local-lift consumer. -/
theorem local_lift_of_double_dimension_mathieu_triple_six
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (model : let D : Type _ := ↥(MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)
      Nonempty (D ≃* Sporadic.Mathieu.M12) ∨ Nonempty (D ≃* Sporadic.Mathieu.M22) ∨
        Nonempty (D ≃* Sporadic.Mathieu.M23) ∨ Nonempty (D ≃* Sporadic.Mathieu.M24) ∨
        Nonempty ((D ⧸ center D) ≃* Sporadic.Mathieu.M22) ∨
        (Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 6)) ∧ Nat.card (center D) = 3)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_double_dimension_mathieu_triple_six hk hd model).elim
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
