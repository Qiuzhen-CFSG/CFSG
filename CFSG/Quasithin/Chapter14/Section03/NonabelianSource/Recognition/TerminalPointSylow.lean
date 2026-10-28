module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalSylow
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankIntersection
public import CFSG.Quasithin.ChapterG.Section10.InvariantGeometry
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# The terminal Sylow lies in the marked point centralizer

The original Sylow preserves E-hat and normalizes the elementary actor.
It therefore preserves the common fixed line in E-hat, which the full
transvection action identifies with the G.10 marked point. A binary line
has only one nonzero vector, so the whole Sylow fixes that point.
Together with terminal actor normality this supplies the literal G.11.1(4)
mark without assumptions on the kernel or center of the original closure.
Source: Aschbacher--Smith, 12.8.12(2), G.11.1(4), and 14.3.15.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem source_terminal_actor_normal_in_point_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T=∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G))={Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (T:Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M)=4)
    (e : (M⧸(centralizer (localModule T M:Set G)).subgroupOf M)≃*Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) :
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    (P:Subgroup F.TerminalHdot)≤ChapterG.Section10.pointCentralizer F.terminalRepresentation v ∧
    F.terminalDot (F.X g)≤(P:Subgroup F.TerminalHdot) ∧
      ((F.terminalDot (F.X g)).subgroupOf (P:Subgroup F.TerminalHdot)).Normal := by
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow
    hG T hempty hM hu hmany hcard e F hne g hgP hgH
  have hPN : (P:Subgroup F.TerminalHdot)≤normalizer (F.terminalDot (F.X g):Set F.TerminalHdot) :=
    (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  have hE := rankTwo_terminal_intersection_invariant
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F hne g hgP hgH
  refine ⟨?_,hXP,hN⟩
  intro t ht
  have hvX : v∈fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) :=
    fun x=>hyp.fixes_point x.property
  have hfv : F.terminalRepresentation t v∈
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) :=
    (fixedSpace_stable_of_normalizes F.terminalRepresentation hPN ht v).2 hvX
  have hEv : F.terminalRepresentation t v∈hatSpace F (F.E g) := hE t ht v hyp.point_mem
  have hvline : F.terminalRepresentation t v∈Submodule.span (ZMod 2) {v} :=
    hyp.fixedSpace_in_W ▸ (show F.terminalRepresentation t v∈
      hatSpace F (F.E g) ⊓ fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) from ⟨hEv,hfv⟩)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hvline
  have hnonzero : F.terminalRepresentation t v≠0 := by
    intro he
    have hh := congrArg (F.terminalRepresentation t⁻¹) he
    have hi : F.terminalRepresentation t⁻¹ (F.terminalRepresentation t v)=v := by
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    rw [hi,map_zero] at hh
    exact hyp.point_ne_zero hh
  have hcne : c≠0 := by intro he;rw[he,zero_smul] at hc;exact hnonzero hc.symm
  have hc1 : c=1 := (by decide : ∀a:ZMod 2,a≠0→a=1) c hcne
  change F.terminalRepresentation t v=v
  simpa only [hc1,one_smul] using hc.symm
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
