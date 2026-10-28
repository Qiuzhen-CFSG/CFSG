module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedAlternatingNatural
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.SelfDual

/-!
# The binary linear rows in the marked two-copy branch

The exact constituent image is self-dual. Its genuine single-component G.9
input excludes the PSL5(2) row and identifies the PSL4(2) row with the natural
A8 action. Transport through the actual orbit map gives two copies on the
whole original space, where the ambient odd-rank and centralizer exclusion
already applies. The theorem concludes the original intrinsic local lift.

Source: Aschbacher–Smith G.11.6–8 and 14.3.15, printed pp.366–369,994.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedAction
variable {D W E U : Type*} [Group D] [Finite D] [Group E]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) D W) (H X : Subgroup D)
  (I : Submodule (ZMod 2) W) (hH : H ≤ subspaceStabilizer ρ I)
  (hX : X ≤ subspaceStabilizer ρ I)

/-- Lift the specified model intertwiner through the literal faithful orbit map. -/
theorem quasiequivalent_of_image
    (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    (τ : Representation (ZMod 2) E U)
    (hq : ChapterG.Section09.Quasiequivalent
      ((kerRepresentation (action ρ H X I hH hX)).comp (image ρ H X I hH hX H).subtype) τ) :
    ChapterG.Section09.Quasiequivalent (invariantSubspace ρ H I hH).toRepresentation τ := by
  let e := subgroupEquiv ρ H X I hH hX hfH H le_rfl
  obtain ⟨a,c,hc⟩ := hq
  refine ⟨e.trans a,c,?_⟩
  intro x w
  exact hc (e x) w
end MarkedAction

namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

private theorem image_selfDual :
    let H := componentOrbit L ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes
    Nonempty (Representation.Equiv ((kerRepresentation σ).comp
      (MarkedAction.image F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes H).subtype)
      (Representation.dual ((kerRepresentation σ).comp
      (MarkedAction.image F.terminalRepresentation H X I s.selected.invariant s.actor_stabilizes H).subtype))) := by
  apply MarkedAction.selfDual_image
  exact (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem).2.2.1

/-- The PSL4(2) row reduces to the checked original doubled A8 exclusion. -/
theorem imageCases_of_double_dimension_binary_four
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        PSL(4, ZMod 2)) : s.ImageCases := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_double_dimension hk hd
  have hs := s.image_selfDual
  dsimp only at hc hs
  rw [← he] at hc
  have hq := ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
    hc hs ((MulEquiv.subgroupCongr he).trans e)
  apply s.imageCases_of_double_dimension_alternating_natural hk hd 8 (by decide) (by decide)
  exact MarkedAction.quasiequivalent_of_image _ _ _ _ _ _
    (s.constituent_faithful _ s.irreducible) _ hq

/-- The original two-copy action has no PSL5(2) component image. -/
theorem not_double_dimension_binary_five
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        PSL(5, ZMod 2)) : False := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_double_dimension hk hd
  have hs := s.image_selfDual
  dsimp only at hc hs
  rw [he] at hc hs
  exact ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.not_five_of_selfDual_sharp_degree
    hc (by have hi := s.dimension_gt_two; omega) hs e

/-- Both larger binary linear rows feed the original intrinsic local lift. -/
theorem local_lift_of_double_dimension_binary_linear
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        PSL(n, ZMod 2)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  rcases hn with rfl | rfl
  · exact s.local_lift_of_image_cases (s.imageCases_of_double_dimension_binary_four hk hd e)
  · exact (s.not_double_dimension_binary_five hk hd e).elim
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
