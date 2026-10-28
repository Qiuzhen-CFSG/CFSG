module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperEight
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperModels

/-!
# TerminalComponentProperEight at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentProperEight`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterB.QuasisimpleSource

open BinaryLinear.OuterCyclic

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V Y W : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem proper_overcomponent_not_eight_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 8)) : False := by
  let := E.actionCentralizer_normal
  let := (P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY.le).quasisimple
  let r := e.toMonoidHom.comp E.coreToFaithful
  have hr' : Function.Surjective r := e.surjective.comp E.coreToFaithful_surjective
  have hi : Function.Injective r := AlternatingEight.reduced_cover_injective r hr'
    (pCore_quotient_pCore_eq_bot 2)
  let cY : (Y ⧸ pCore 2 Y) ≃* LinearGroup 4 :=
    (MulEquiv.ofBijective r ⟨hi,hr'⟩).trans
      (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
        (projectiveEquivLinear (by decide : 0 < 4)))
  let J := Y ⊔ (T : Subgroup G)
  let C := Y.subgroupOf J
  let B := P.K.subgroupOf J
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hKJ : P.K ≤ J := hKY.le.trans le_sup_left
  let cC : C ≃* Y := subgroupOfEquivOfLe le_sup_left
  let cB : B ≃* P.K := subgroupOfEquivOfLe hKJ
  let eC : (C ⧸ pCore 2 C) ≃* LinearGroup 4 :=
    (QuotientGroup.congr _ _ cC (pCore_map_iso 2 _)).trans cY
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer E.sylow_normalizes_component)
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.1
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect
    (P.residual_local_and_quasisimple_at structural modules hr hw).1
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := cC.symm.toMonoidHom) cC.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := cB.symm.toMonoidHom) cB.symm.surjective
  have hgen : C ⊔ (U : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left]
    change Y ⊔ ((T : Subgroup G).subgroupOf J).map J.subtype = _
    rw [map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  have hBC : B ≤ C := comap_mono hKY.le
  have hne : B ≠ C := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hKJ,map_subgroupOf_eq_of_le le_sup_left] at hh
    exact hKY.ne hh
  have hns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable
      (P.residual_local_and_quasisimple_at structural modules hr hw).1
      (Group.isSolvable_of_surjective (f := cB.toMonoidHom) cB.surjective)
  have hUB : (U : Subgroup J) ≤ normalizer (B : Set J) :=
    (comap_mono P.sylow_normalizes_residual).trans (le_normalizer_comap J.subtype)
  obtain ⟨a,ha,hka⟩ := BinaryLinear.SylowFlagOvergroups.exists_inner_four_core_action
    C eC U hgen B hBC hne hns hUB
  have hHJ : P.H ≤ J := by
    rw [← P.residual_sup_sylow]
    exact sup_le_sup hKY.le le_rfl
  let A := P.H.subgroupOf J
  let c : A ≃* P.H := subgroupOfEquivOfLe hHJ
  have hUA : (U : Subgroup J) ≤ A := fun _ ht => P.minimal.1.1.2 ht
  have hu := ((P.minimalParabolic_at structural hw).1).map c.symm.mapSubgroup
  have heU : ((T.subtype P.minimal.1.1.2 : Subgroup P.H)).map c.symm.toMonoidHom =
      (U : Subgroup J).subgroupOf A := by
    ext x
    rw [mem_map_equiv]
    rfl
  change Order.HasUniqueMaximalOver
    ((T.subtype P.minimal.1.1.2 : Subgroup P.H).map c.symm.toMonoidHom)
    ((⊤ : Subgroup P.H).map c.symm.toMonoidHom) at hu
  rw [heU,map_top_of_surjective _ c.symm.surjective] at hu
  let : Group.IsSolvable A :=
    BinaryLinear.SylowFlagOvergroups.solvable_of_two_kernel_uniqueMaximal a ha hka U A hUA hu
  exact P.not_solvable_at structural hr hw
    (Group.isSolvable_of_surjective (f := c.toMonoidHom) c.surjective)

theorem proper_overcomponent_seven_model_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal;
      Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
        alternatingGroup (Fin 7)) := by
  let := E.actionCentralizer_normal
  cases P.proper_overcomponent_alternating_alternatives_at structural modules hr hw hY hKY E with
  | alternating n hn action =>
    rcases hn with rfl | rfl
    · exact ⟨action.groupEquiv⟩
    · exact (P.proper_overcomponent_not_eight_at structural modules hr hw hY hKY E action.groupEquiv).elim
  | alternatingSevenFour e _ => exact ⟨e⟩

theorem proper_overcomponent_setup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hKY : P.K < Y) :
    ∃ W : Subgroup G, Nonempty (Setup T Y W) := by
  have h := P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY.le
  obtain ⟨W,⟨E⟩⟩ := (structural Y h).2.1
  obtain ⟨e⟩ := P.proper_overcomponent_seven_model_at structural modules hr hw hY hKY E
  obtain ⟨c⟩ := P.proper_overcomponent_seven_central_quotient_at structural modules hr hw hY hKY E e
  exact ⟨W,⟨⟨h,E,c⟩⟩⟩

theorem componentAnalysis_of_residual_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models_at structural modules escape localAnalysis_at hr hw
  intro Y hY hKY
  obtain ⟨W,⟨SY⟩⟩ := P.proper_overcomponent_setup_at structural modules hr hw hY hKY
  exact ⟨⟨q⟩,⟨SY.quotient⟩⟩

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

