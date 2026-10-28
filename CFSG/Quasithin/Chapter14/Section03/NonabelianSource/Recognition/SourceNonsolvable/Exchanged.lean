module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Containment
public import CFSG.Quasithin.ChapterG.Section10.Components.Exchanged

/-!
# Exchanged-constituent geometry in the original terminal action

The original terminal representation supplies the point-Sylow normality and
component-normalizer bound needed by G.10.15's two-summand argument. For its
selected homogeneous constituent avoiding the marked point, the actual actor
stabilizer has index two and induces the full centered transvection group on
the constituent's intersection with the marked axis. The half-point spans the
intersection with the original hat space of E.

This is the geometry before the non-GL assertion G.10.15(3): no equality of
the constituent orbit with the ambient module or faithfulness consequence is
assumed. Source: Aschbacher--Smith G.10.15(1)(ii), G.11.7 and 14.3.15,
printed pp.361--362,366--367,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exchanged alternative for the literal original terminal action,
with the Sylow and component-normalizer inputs discharged at their source. -/
theorem source_terminal_exchanged_constituent_geometry
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
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
      (componentOrbit L ⊤) (F.terminalDot (F.X g)) I)
    (hv : v ∉ I) :
    ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I := by
  let S : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,hXP,hN⟩ := source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp
  exact hyp.exchanged_constituent_geometry hn hL hm S
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
    (terminal_component_normalizer_index_le_two hG F (by decide) L hL) hI hv

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
