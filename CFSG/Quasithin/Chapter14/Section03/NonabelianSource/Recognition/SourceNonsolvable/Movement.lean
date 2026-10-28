module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Original
public import CFSG.Quasithin.ChapterG.Section10.Components.Movement

/-!
# Movement on the original nonsolvable constituent orbit

The original point-Sylow normality and the component-orbit bound discharge
the group-theoretic premises of the G.10.10 movement argument. Every nonzero
subspace invariant under the selected component's normal orbit is moved by
the literal terminal X. The selected component and its actual G.10 hypothesis
are supplied by `source_terminal_component_extraction`.

Source: Aschbacher--Smith G.10.10 and14.3.15, printed pp.360,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- G.10.10's movement assertion on the original terminal constituent orbit.
The Sylow and component-orbit conditions are proved from the source context. -/
theorem source_terminal_component_subspace_not_fixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (U : Submodule (ZMod 2) (Additive F.Uhat))
    (hU : componentOrbit L ⊤ ≤ subspaceStabilizer F.terminalRepresentation U)
    (hU0 : U ≠ ⊥) : ¬ U ≤ fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) := by
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,hXP,hN⟩ := source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp
  exact hyp.normal_component_subspace_not_fixed hn hL hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
    (terminal_component_normalizer_index_le_two hG F (by decide) L hL) U hU hU0

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
