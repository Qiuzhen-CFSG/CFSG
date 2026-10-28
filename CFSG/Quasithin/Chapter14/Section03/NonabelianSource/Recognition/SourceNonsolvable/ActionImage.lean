module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Containment
public import CFSG.Quasithin.ChapterG.Section10.Components.Homogeneous
public import CFSG.Quasithin.ChapterG.Section10.Components.ActionImage
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.Isotropic
/-!
# The original G.11.7 constituent action and its rank-one exclusion

For the original terminal representation the point-Sylow normality,
component-orbit bound, homogeneity and the genuine SQTK cover supply all
fields of G.9.3 on Aut_HX(I). The quotient is the kernel quotient of the
literal action on I, and its marked subgroups are actual images.

When I is isotropic its degree is at most m(X)+1. The proved SL₂ module
alternatives exclude the single binary rank-one component rows under the
source contradiction assumption that X acts faithfully on I. Other rows
and the exchanged-constituent geometry remain separate source arguments.
Source: Aschbacher--Smith G.11.7 and14.3.15, printed pp.366–367,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- All G.9.3 fields on the actual original constituent action quotient. -/
theorem source_terminal_constituent_action_componentHypothesis
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
    (hfX : Function.Injective (fun x : F.terminalDot (F.X g) =>
      (F.terminalRepresentation (x : F.TerminalHdot)).comp I.subtype)) :
    let H := componentOrbit L ⊤
    letI : H.Normal := componentOrbit_top_normal L
    let hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hn) H hI hv
    let σ := ChapterG.Section09.constituentAction F.terminalRepresentation H
      (F.terminalDot (F.X g)) I hI.choose hXI
    let P := H ⊔ F.terminalDot (F.X g)
    let q := QuotientGroup.mk' σ.ker
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      (Representation.kerRepresentation σ) (((F.terminalDot (F.X g)).subgroupOf P).map q)
      ((L.subgroupOf P).map q) ((H.subgroupOf P).map q)
      (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  let S : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨_,hXP,hN⟩ := source_terminal_actor_normal_in_point_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hyp
  exact hyp.componentHypothesis_of_marked_constituent
    ⟨terminal_sqtkCover hG F (by decide)⟩ hn hL hm S
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN)
    (terminal_component_normalizer_index_le_two hG F (by decide) L hL) hI hv hfX

/-- The faithful-X isotropic branch cannot have a single binary SL₂
component. The group isomorphism is to the literal image component. -/
theorem source_terminal_isotropic_constituent_excludes_rank_one
    {k : Type*} [Field k] [Finite k] [CharP k 2]
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
    (hfX : Function.Injective (fun x : F.terminalDot (F.X g) =>
      (F.terminalRepresentation (x : F.TerminalHdot)).comp I.subtype))
    (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0) :
    let H := componentOrbit L ⊤
    letI : H.Normal := componentOrbit_top_normal L
    let hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hn) H hI hv
    let σ := ChapterG.Section09.constituentAction F.terminalRepresentation H
      (F.terminalDot (F.X g)) I hI.choose hXI
    let P := H ⊔ F.terminalDot (F.X g)
    let q := QuotientGroup.mk' σ.ker
    ∀ (_hHL : (H.subgroupOf P).map q = (L.subgroupOf P).map q)
      (_er : ((L.subgroupOf P).map q) ≃* SL(2,k)) (n : ℕ),
      2 ≤ n → Nat.card k = 2^n → False := by
  intro H hXI σ P q hHL er n hnfield hfield
  have hc := source_terminal_constituent_action_componentHypothesis
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hL hm hI hv hfX
  change ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
    (Representation.kerRepresentation σ) (((F.terminalDot (F.X g)).subgroupOf P).map q)
    ((L.subgroupOf P).map q) ((H.subgroupOf P).map q)
    (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) at hc
  rw [hHL] at hc
  exact hc.not_rank_one_of_degree_le_rank_add_one
    (hyp.isotropic_degree_le_actor_rank_add_one hiso) er n hnfield hfield

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
