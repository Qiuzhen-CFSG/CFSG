module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SingleComponentReduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.PointRanks
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.SelfDual
public import Theory.Representation.BinaryPermutation.EightCentralizer
public import Theory.Representation.BinaryNaturalDual.Transport
public import Theory.Representation.BinaryPermutation.PointStabilizerRank

/-!
# Excluding the whole A₈ component on the original extraspecial flag

When Z(U) is the original point, its order two makes all of H centralize it.
The proved source point-centralizer bound therefore applies to the whole
terminal point stabilizer. The genuine A₈ six-space has point stabilizers
of three-rank at least two, contradicting that bound. The component's
natural coordinates come from G.9 recognition and the original alternating
form, rather than an assumed action model.

The final theorem refines the original single-component reduction. The
remaining component and multiplicity branches are still required for the
marked large-case catalogue.

Source: Aschbacher--Smith 12.8.13(8), 14.3.13 and 14.4.2,
printed pp.855--856,993--994,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the extraspecial branch the actual whole A₈ component contradicts
the source point-centralizer three-rank bound. -/
theorem source_no_alternating_eight_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* alternatingGroup (Fin 8)) : False := by
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  obtain ⟨e,c,hc⟩ :=
    ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
      h9 (ChapterG.Section11.LargeWhole.selfDual hyp)
      (e₀.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  let P := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (P.subgroupOf D) ≤ 1 at hu
  have hpD : P ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  have hr : 2 ≤ primeRank 3 (P.subgroupOf C) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp C.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c hc v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let j : P.subgroupOf C →* P := {
    toFun a := ⟨a.val.val,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : P => z.val) he))
  have hh := Theory.GroupTheory.primeRank_le_of_injective 3 j hj
  omega

/-- The original normal irreducible component branch now retains only A₇,
G₂(2)′, fixed-line M₂₂ and the triple-M₂₂ cover in degree twelve. -/
theorem source_large_single_component_models (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) :
    (IsSimpleGroup C ∧
      (Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
        (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
          Nonempty (C ≃* Sporadic.Mathieu.M22)))) ∨
    (Chapter1.Section02.LocalModels.IsM22Cover C ∧ finrank (ZMod 2) (Additive F.Uhat) = 12) := by
  rcases source_large_single_component_reduction d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH C hC hm hirr with ⟨hi,hsmall | hfixed⟩ | hcover
  · refine .inl ⟨hi,?_⟩
    cases hsmall with
    | seven he => exact .inl he
    | eight he => exact (source_no_alternating_eight_component d earlier hq chosen structural
        alternatives F hne hZ g hgP hgH C hC hm hirr he.some).elim
    | binary_g2 he => exact .inr (.inl he)
  · exact .inl ⟨hi,.inr (.inr hfixed)⟩
  · exact .inr hcover
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
