module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Containment
public import CFSG.Quasithin.ChapterG.Section10.Components.Homogeneous
public import CFSG.Quasithin.ChapterG.Section10.Components.Source
/-!
# The original marked homogeneous constituent and its G.9 consumer

On the terminal representation from the original selected rank-two data,
a constituent containing the marked point is the unique occurring simple
type for its normal component orbit. The original point-Sylow normality and
component-orbit bound discharge the G.10 geometric inputs. The actual
restricted action is faithful and self-dual, and its form is totally isotropic
unless the constituent is the whole hat module.

In the nondegenerate branch the latter conclusion gives the exact
G.9.ComponentHypothesis for the original terminal action and elementary X.
Its cover is the actual point normalizer with the literal terminal quotient
map. Source: Aschbacher--Smith G.10.13,G.10.15(I),G.11.7 and14.3.15,
printed pp.360--361,366,994. The exchanged-constituent branch and the subsequent
component-model classification remain separate source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual marked constituent is homogeneous, faithful and self-dual;
its form is either totally isotropic or its space is the original whole hat module. -/
theorem source_terminal_constituent_homogeneous_of_point_mem
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
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) I)
    (hv : v ∈ I) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧
      Function.Injective R.toRepresentation ∧
      Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
      ((∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∨
        (I = ⊤ ∧ Representation.IsIrreducible
          (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype))) := by
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,hXP,hN⟩ := source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp
  exact hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hL hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
    (terminal_component_normalizer_index_le_two hG F (by decide) L hL) hI hv

/-- In the nondegenerate marked-constituent branch, all premises of G.9.3
are supplied for the literal terminal representation, cover and original X. -/
theorem source_terminal_componentHypothesis_of_marked_nondegenerate
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
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) I)
    (hv : v ∈ I)
    (hnd : (B.restrict I).Nondegenerate) :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  have hd := (source_terminal_constituent_homogeneous_of_point_mem
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hL hm hI hv).2.2.2
  have hi : Representation.IsIrreducible
      (F.terminalRepresentation.comp (componentOrbit L ⊤).subtype) := by
    rcases hd with hiso | ⟨_,hirr⟩
    · have hz : (⟨v,hv⟩ : I) = 0 := hnd.1 ⟨v,hv⟩ (fun w => hiso v hv w w.property)
      exact (hyp.point_ne_zero (congrArg Subtype.val hz)).elim
    · exact hirr
  exact hyp.componentHypothesis_of_orbit_irreducible
    ⟨terminal_sqtkCover hG F (by decide)⟩ hL hm
    (terminal_component_normalizer_index_le_two hG F (by decide) L hL) hi

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
