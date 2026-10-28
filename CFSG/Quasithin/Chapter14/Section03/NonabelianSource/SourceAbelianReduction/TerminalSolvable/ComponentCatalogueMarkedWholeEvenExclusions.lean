module
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentSharpExclusions
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.SelfDual
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentEvenExclusions
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Theory.Representation.Quotient
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedCoefficientField

/-!
# Whole marked even-degree exclusions

The original whole constituent has even dimension and is self-dual. Transport
along its literal component-image equivalence therefore excludes the M₂₃,
M₂₄ and SL₅(2) rows, and supplies the original local component lift in each
of those impossible cases.

Source: Aschbacher--Smith G.11.7 and 14.3.15.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open scoped MatrixGroups
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [_root_.Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

theorem not_whole_even_models (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    (model : Nonempty (L ≃* Sporadic.Mathieu.M23) ∨ Nonempty (L ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (L ≃* PSL(5,ZMod 2))) : False := by
  have hf : ActorFaithful (F := F) (g := g) (I := I) := by
    by_contra hn
    exact s.constituent_ne_top_of_not_actorFaithful hn hi
  have hc := s.componentHypothesis_of_actorFaithful hf
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hs := MarkedAction.selfDual_image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (Recognition.source_terminal_constituent_homogeneous_of_point_mem
      s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
      s.selected.isIrrPlus s.point_mem).2.2.1
  dsimp only at hc hs
  rw [he] at hc hs
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  have heven : Even (finrank (ZMod 2) I) := by
    rw [hi,finrank_top,s.actor_dimension]
    exact even_two_mul _
  apply hc.not_even_models heven hs
  rcases model with h23 | h24 | h5
  · exact Or.inl ⟨eL.symm.trans h23.some⟩
  · exact Or.inr (Or.inl ⟨eL.symm.trans h24.some⟩)
  · exact Or.inr (Or.inr ⟨eL.symm.trans h5.some⟩)

theorem local_lift_of_whole_even_models (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    (model : Nonempty (L ≃* Sporadic.Mathieu.M23) ∨ Nonempty (L ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (L ≃* PSL(5,ZMod 2))) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_even_models hi hHL model).elim
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
