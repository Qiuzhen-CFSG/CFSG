module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperExterior
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.FourExtension
public import Theory.SpecificGroups.AlternatingEight.ReducedCover
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalLift

/-!
# The proper H-star overcomponent has alternating-seven quotient

The reduced-cover theorem removes the center above the literal A₈ action.
Under A₈ ≃ SL₄(2), preservation of the proper nonsolvable component forces
the Sylow action to be inner. The resulting full binary action has a
two-group kernel, contradicting H-star minimal parabolicity by flag geometry.
Thus every proper overcomponent has the A₇ faithful quotient, with the
original natural central action or four-dimensional chosen space. The odd-degree
central-cover theorem lifts the natural section to the whole chosen space,
giving dimension six in that row.

The final theorem applies this restriction to the guarded source residual
construction. The residual A₅ marking, H-star module restrictions and final
nonsolvable exclusion remain with qt-d-12213-hstar-natural. Source:
Aschbacher–Smith, 12.2.7, printed pp.797–798.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource ChapterI.Section06To08
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H X Y W : Subgroup G}

/-- A proper A₈ overcomponent is incompatible with the original H-star group. -/
theorem HStarGeneratingComponent.not_eight_overcomponent_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 8)) : False := by
  let := E.actionCentralizer_normal
  let := hY.quasisimple
  let r := e.toMonoidHom.comp E.coreToFaithful
  have hr' : Function.Surjective r := e.surjective.comp E.coreToFaithful_surjective
  have hi : Function.Injective r := AlternatingEight.reduced_cover_injective r hr'
    (pCore_quotient_pCore_eq_bot 2)
  let cY : (Y ⧸ pCore 2 Y) ≃* LinearGroup 4 :=
    (MulEquiv.ofBijective r ⟨hi,hr'⟩).trans
      (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
        (projectiveEquivLinear (by decide : 0 < 4)))
  let J := Y ⊔ (T : Subgroup G)
  let A := Y.subgroupOf J
  let B := X.subgroupOf J
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hKJ : X ≤ J := hXY.le.trans le_sup_left
  let cC : A ≃* Y := subgroupOfEquivOfLe le_sup_left
  let cB : B ≃* X := subgroupOfEquivOfLe hKJ
  let eC : (A ⧸ pCore 2 A) ≃* LinearGroup 4 :=
    (QuotientGroup.congr _ _ cC (pCore_map_iso 2 _)).trans cY
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer E.sylow_normalizes_component)
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.maximal_faithful.1.1
  let : Group.IsPerfect X := Chapter1.mem_L_isPerfect
    (C.exists_maximal_overcomponent hH).1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := cC.symm.toMonoidHom) cC.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := cB.symm.toMonoidHom) cB.symm.surjective
  have hgen : A ⊔ (U : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left]
    change Y ⊔ ((T : Subgroup G).subgroupOf J).map J.subtype = _
    rw [map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  have hBC : B ≤ A := comap_mono hXY.le
  have hne : B ≠ A := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hKJ,map_subgroupOf_eq_of_le le_sup_left] at hh
    exact hXY.ne hh
  have hns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable
      (C.exists_maximal_overcomponent hH).1
      (Group.isSolvable_of_surjective (f := cB.toMonoidHom) cB.surjective)
  have hUB : (U : Subgroup J) ≤ normalizer (B : Set J) :=
    (comap_mono (C.normalized_of_overcomponent_at structural modules hH hXY.le hY)).trans (le_normalizer_comap J.subtype)
  obtain ⟨a,ha,hka⟩ := BinaryLinear.SylowFlagOvergroups.exists_inner_four_core_action
    A eC U hgen B hBC hne hns hUB
  exact C.not_binary_join_actor_at h D structural hTI hH hXY.le a ha hka

/-- Every chosen module of a proper H-star overcomponent has the actual
A₇ action quotient and either its natural central section or dimension four. -/
theorem HStarGeneratingComponent.proper_seven_rows_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal
    Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) ∧
      (Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 7)) ∨
        Module.finrank (ZMod 2) E.space = 4) := by
  let := E.actionCentralizer_normal
  rcases C.proper_alternating_rows_at h D structural modules hTI hH hXY hY E with
    ⟨n,hn,⟨e⟩⟩ | ⟨e,hd⟩
  · rcases hn with rfl | rfl
    · exact ⟨⟨e.groupEquiv⟩,Or.inl ⟨e⟩⟩
    · exact (C.not_eight_overcomponent_at h D structural modules hTI hH hXY hY E e.groupEquiv).elim
  · exact ⟨e,Or.inr hd⟩

/-- The original guarded residual construction now has only the equal A₅
or proper A₇ overcomponent cases. This does not assume a model for the residual. -/
theorem chosen_hstar_residual_overcomponent_five_or_seven_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X ≤ Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      ((X = Y ∧ Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) ∧
          ∀ (W : Subgroup G) (E : ChosenModule T Y W), letI := E.actionCentralizer_normal
            Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 5))) ∨
        (X < Y ∧ ∀ (W : Subgroup G) (E : ChosenModule T Y W),
          letI := E.actionCentralizer_normal
          Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) ∧
            (Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 7)) ∨
              Module.finrank (ZMod 2) E.space = 4))) := by
  obtain ⟨X,Y,C,hr,hXY,hY⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  refine ⟨X,Y,C,hr,hXY,hY,?_⟩
  by_cases he : X = Y
  · obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
    have hf := (C.five_of_eq_at h D structural modules hTI hH hY he E).1
    refine Or.inl ⟨he,he.symm ▸ hf,?_⟩
    exact fun _ E => (C.five_of_eq_at h D structural modules hTI hH hY he E).2
  · have hlt := lt_of_le_of_ne hXY he
    exact Or.inr ⟨hlt,fun _ E => C.proper_seven_rows_at h D structural modules hTI hH hlt hY E⟩

/-- The faithful seven-letter quotient is the literal quotient by O₂,Z(Y),
and the original chosen space has rank four or six. -/
theorem HStarGeneratingComponent.proper_seven_source_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) ∧
      (T : Subgroup G) ≤ normalizer (W : Set G) ∧
      (Module.finrank (ZMod 2) E.space = 4 ∨ Module.finrank (ZMod 2) E.space = 6) := by
  let := E.actionCentralizer_normal
  let := hY.quasisimple
  obtain ⟨⟨e⟩,hrows⟩ := C.proper_seven_rows_at h D structural modules hTI hH hXY hY E
  let r := e.toMonoidHom.comp E.coreToFaithful
  have hr : Function.Surjective r := e.surjective.comp E.coreToFaithful_surjective
  have hk : r.ker = center (Y ⧸ pCore 2 Y) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7)),MonoidHom.comap_bot] at hh
    exact hh
  let f := r.comp (QuotientGroup.mk' (pCore 2 Y))
  have hf : Function.Surjective f := hr.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = centralPreimage (pCore 2 Y) := by
    change r.ker.comap (QuotientGroup.mk' (pCore 2 Y)) = _
    rw [hk]
    rfl
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩,((structural Y hY).2.2 W E).1,?_⟩
  rcases hrows with ha | hd
  · obtain ⟨a⟩ := ha
    obtain ⟨b⟩ := E.fullAction_of_odd_alternating_quotient (by decide) (by decide) a
    right
    calc
      Module.finrank (ZMod 2) E.space =
          Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 7)) := b.linearEquiv.finrank_eq
      _ = 6 := by simpa using BinaryPermutation.finrank_natural_odd (Ω := Fin 7) (by decide)
  · exact Or.inl hd

/-- The proper branch of the original residual construction has precisely
the central quotient, invariance and ranks required in source 12.2.7(3ii). -/
theorem chosen_hstar_overcomponent_source_cases_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X ≤ Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      ((X = Y ∧ Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))) ∨
        (X < Y ∧ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) ∧
          ∀ (W : Subgroup G) (E : ChosenModule T Y W),
            (T : Subgroup G) ≤ normalizer (W : Set G) ∧
            (Module.finrank (ZMod 2) E.space = 4 ∨ Module.finrank (ZMod 2) E.space = 6))) := by
  obtain ⟨X,Y,C,hr,hXY,hY,hcases⟩ :=
    chosen_hstar_residual_overcomponent_five_or_seven_of_many_at
      h D structural modules hmany hnone hTI hH hs
  refine ⟨X,Y,C,hr,hXY,hY,?_⟩
  rcases hcases with ⟨he,hf,_⟩ | ⟨hlt,_⟩
  · exact Or.inl ⟨he,hf⟩
  · obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
    refine Or.inr ⟨hlt,(C.proper_seven_source_at h D structural modules hTI hH hlt hY E).1,?_⟩
    exact fun _ E => (C.proper_seven_source_at h D structural modules hTI hH hlt hY E).2

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
