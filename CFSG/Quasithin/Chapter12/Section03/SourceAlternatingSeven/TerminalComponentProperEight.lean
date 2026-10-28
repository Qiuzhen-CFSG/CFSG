module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperModels
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.FourExtension
public import Theory.SpecificGroups.AlternatingEight.ReducedCover

/-!
# Excluding A₈ and constructing the proper A₇ overcomponent setup

The faithful A₈ marking identifies Y/O₂(Y) with A₈: the reduced-cover
theorem removes the central kernel. Under A₈ ≃ SL₄(2), a Sylow-preserving
outer automorphism cannot preserve the proper nonsolvable residual image.
The ambient action is therefore inner, and lifts to YT with a two-group
kernel. Binary flag geometry then makes the original minimal parabolic H
solvable, contradicting its source nonsolvability.

Every proper maximal overcomponent consequently has the original A₇ setup,
including the literal central quotient. The final application constructs
all fields of ComponentAnalysis from the single remaining residual quotient
identification. That identification is still an obligation of
qt-d-1231-terminal-component; the conditional application is not the
completed source theorem.

Source: Aschbacher–Smith, 12.2.7, printed pp.797–798, and 12.3.12, p.811.
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

/-- The actual terminal minimal parabolic excludes a proper A₈ overcomponent. -/
theorem proper_overcomponent_not_eight
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 8)) : False := by
  let := E.actionCentralizer_normal
  let := (P.residual_overgroup_hypothesis structural modules hr hw hY hKY.le).quasisimple
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
    (P.residual_local_and_quasisimple structural modules hr hw).1
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
      (P.residual_local_and_quasisimple structural modules hr hw).1
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
  have hu := ((P.minimalParabolic structural hw).1).map c.symm.mapSubgroup
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
  exact P.not_solvable structural hr hw
    (Group.isSolvable_of_surjective (f := c.toMonoidHom) c.surjective)

/-- Every proper maximal overcomponent has the actual faithful A₇ marking. -/
theorem proper_overcomponent_seven_model
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hKY : P.K < Y) (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal;
      Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
        alternatingGroup (Fin 7)) := by
  let := E.actionCentralizer_normal
  cases P.proper_overcomponent_alternating_alternatives structural modules hr hw hY hKY E with
  | alternating n hn action =>
    rcases hn with rfl | rfl
    · exact ⟨action.groupEquiv⟩
    · exact (P.proper_overcomponent_not_eight structural modules hr hw hY hKY E action.groupEquiv).elim
  | alternatingSevenFour e _ => exact ⟨e⟩

/-- The original 12.2.3 setup for every proper maximal overcomponent,
without first recognizing the residual quotient. -/
theorem proper_overcomponent_setup
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hKY : P.K < Y) :
    ∃ W : Subgroup G, Nonempty (Setup T Y W) := by
  have h := P.residual_overgroup_hypothesis structural modules hr hw hY hKY.le
  obtain ⟨W,⟨E⟩⟩ := (structural G T Y h).2.1
  obtain ⟨e⟩ := P.proper_overcomponent_seven_model structural modules hr hw hY hKY E
  obtain ⟨c⟩ := P.proper_overcomponent_seven_central_quotient structural modules hr hw hY hKY E e
  exact ⟨W,⟨⟨h,E,c⟩⟩⟩

/-- Apply the completed overcomponent classification to all original
component-analysis conclusions. Only recognition of the residual in an
actual A₇ setup remains with the terminal-component assembly owner. -/
theorem componentAnalysis_of_residual_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models structural modules escape localAnalysis hr hw
  intro Y hY hKY
  obtain ⟨W,⟨SY⟩⟩ := P.proper_overcomponent_setup structural modules hr hw hY hKY
  exact ⟨⟨q⟩,⟨SY.quotient⟩⟩

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
