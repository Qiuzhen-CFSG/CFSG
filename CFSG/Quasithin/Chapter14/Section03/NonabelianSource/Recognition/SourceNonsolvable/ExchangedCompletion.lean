module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Containment
public import CFSG.Quasithin.ChapterG.Section10.Components.ExchangedCompletion

/-!
# Completion of the original terminal exchanged constituent

The terminal source supplies the Sylow normality and component-normalizer
bound. Conditional only on the actual component action being proper in GL(I),
G.10.15(3), the exchanged orbit spans the original terminal module and the
literal stabilizer N_X(I) acts faithfully on both I and the component orbit.

Source: Aschbacher--Smith G.10.15(1)(ii), its implication from (3), and
14.3.15, printed pp.361--362 and 994. The separate non-GL assertion is an
explicit premise for its independent source producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal terminal exchanged alternative, conditional on G.10.15(3). -/
theorem source_terminal_exchanged_constituent_completion
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
    (hv : v ∉ I)
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        hI.invariant).toRepresentation.asGroupHom) :
    ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
    Homogeneous.orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I = ⊤ ∧
    let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))
    (∀ y : Y, (∀ u : I, F.terminalRepresentation ((y : F.terminalDot (F.X g)) : F.TerminalHdot) u = u) → y = 1) ∧
    (∀ y : Y, ((y : F.terminalDot (F.X g)) : F.TerminalHdot) ∈
      centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) → y = 1) := by
  let S : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,hXP,hN⟩ := source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp
  exact hyp.exchanged_constituent_completion hn hL hm S
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
    (terminal_component_normalizer_index_le_two hG F (by decide) L hL) hI hv hproper

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
