module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceMovement
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourcePlacement
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSeven.SmallImage

/-!
# The original H-star residual is A₅ modulo its own two-core

The proper-overcomponent argument already supplies either the A₅ quotient
or a literal seven-letter alternating action with solvable kernel. In the
latter branch the normal Sylow supplement has a proper perfect image.
The seven-letter subgroup calculation excludes A₆ and PSL₃(2), and the
A₅ central-cover calculation recovers the intrinsic quotient of the original
component. Together with its literal identification with O²(H), this proves
12.2.7(2) under the same ambient multiple-overgroup guard used in the source.

The quotient-rank and V ≤ O²(H)O₂(H) applications retain the original groups
and maps. Whole-module restrictions and the TI-pair argument in 12.2.19
remain with qt-d-12213-hstar-natural.
Source: Aschbacher–Smith, 12.2.7 and 12.2.19, printed pp.797–798 and 801.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X Y : Subgroup G}

/-- Identify the original component through the actual alternating action.
The kernel may be solvable; it is not assumed to be a two-group. -/
theorem HStarGeneratingComponent.five_of_alternating_action_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (f : H →* alternatingGroup (Fin 7)) (hk : Group.IsSolvable f.ker) :
    Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) := by
  let S := T.subtype hH.1.1.2
  let K := X.subgroupOf H
  let e : K ≃* X := subgroupOfEquivOfLe C.component.1
  let : K.Normal := normal_subgroupOf_of_le_normalizer (by
    rw [←C.generates]
    exact sup_le X.le_normalizer hTX)
  let : Group.IsPerfect X := Chapter1.mem_L_isPerfect (C.exists_maximal_overcomponent hH).1
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let := C.quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm))
  have hgen : K ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le C.component.1]
    change X ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = _
    rw [map_subgroupOf_eq_of_le hH.1.1.2,C.generates,←MonoidHom.range_eq_map,range_subtype]
  have hs : ¬ Group.IsSolvable K := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable (C.exists_maximal_overcomponent hH).1
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  obtain ⟨q⟩ := ChapterB.AlternatingSevenImage.normal_supplement_core_five S
    (chosen_hstar_minimalParabolic_at h D structural hTI hH) K hgen hs f hk
  exact ⟨(QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans q⟩

/-- Both equal and proper overcomponents give the same actual A₅ residual quotient. -/
theorem HStarGeneratingComponent.five_of_overcomponent_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) :
    Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) := by
  by_cases he : X = Y
  · obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
    exact he.symm ▸ (C.five_of_eq_at h D structural modules hTI hH hY he E).1
  rcases C.proper_five_or_alternating_action_at h D structural modules hTI hH
      (lt_of_le_of_ne hXY he) hY with hf | ⟨f,hf⟩
  · exact hf
  · exact C.five_of_alternating_action_at h D structural hTI hH
      (C.normalized_of_overcomponent_at structural modules hH hXY hY) f hf

/-- Source 12.2.7(2) on the literal O²(H), with its intrinsic two-core. -/
theorem chosen_hstar_residual_five_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨X,Y,C,hr,hXY,hY⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  obtain ⟨f⟩ := C.five_of_overcomponent_at h D structural modules hTI hH hXY hY
  let e : pResidual 2 H ≃* X :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hr.symm)
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans f⟩

/-- The original quotient-rank conclusion now has no residual-identification premise. -/
theorem chosen_hstar_quotient_rank_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
  apply chosen_hstar_quotient_rank_of_residual_identification_at h D structural hTI hH
  exact fun hs => chosen_hstar_residual_five_of_many_at h D structural modules hmany hnone hTI hH hs

/-- The actual TI-pair setup of 12.2.19 now has its residual placement. -/
theorem chosen_hstar_le_residual_join_core_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    V ≤ (pResidual 2 H).map H.subtype ⊔ H.pCoreIn 2 := by
  obtain ⟨e⟩ := chosen_hstar_residual_five_of_many_at h D structural modules hmany hnone hTI hH hs
  exact chosen_hstar_le_residual_join_core_at h D structural hH e

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
