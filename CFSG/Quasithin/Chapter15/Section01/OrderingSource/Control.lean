module
public import CFSG.Quasithin.Chapter15.Section01.CentralizingControl
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Ordering
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Solvable.Baumann
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Ordering control from a centralizing maximal local subgroup

The centralizing branch of the local ordering follows from the actual Thompson
normalizer control. For a minimal parabolic, a moved reduced module supplies the
Baumann Sylow condition; the common-normal theorem then places the parabolic in
the selected maximal local subgroup. Finally A.5.6 excludes an invariant span of
a nontrivial Sylow-central seed once the local ordering has been established.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, original
14.1.4 and A.5.6. These are the control and final span steps of 14.1.4; the
production of the moved reduced module is a separate input to the middle step.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem source_centralizing_local_ordering
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hN : N ∈ maximalLocals T)
    (hJN : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T N : Set G)) :
    OrderingLE T N M := by
  have hn := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.1
  apply UniformControl.source_centralizing_ordering hG T hN hJN
    (⊤ : Subgroup (baumann (T : Subgroup G)))
  simpa only [← MonoidHom.range_eq_map,range_subtype] using hn

theorem source_minimalParabolic_le_of_baumann_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hP : IsMinimalParabolicOver T H)
    (hs : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      ((pResidual 2 H).map H.subtype ⊔ baumann (T : Subgroup G))) : H ≤ M := by
  obtain ⟨_,_,hu,_,hn,_,_⟩ := source_centralizing_baumann_control hG T hM hJ
  let A := M ⊓ normalizer (baumann (T : Subgroup G) : Set G)
  have hTA : (T : Subgroup G) ≤ A :=
    le_inf hM.1.2 (le_normalizer.trans (normalizer_le_normalizer_baumann _))
  have hA : A ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTA inf_le_left
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ h => h.1
  have hBne : baumann (T : Subgroup G) ≠ ⊥ := by
    intro he
    apply centralInvolutions_ne_bot_of_maximal_local T hM.1
    apply bot_unique
    apply le_trans _ he.le
    exact le_inf (fun z hz => ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
      (fun z hz x hx => (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 x
        (show x ∈ (T : Subgroup G) from
          hJT ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1)))
  have hc := Chapter3.source_common_normal_knownSimple hG T A H _ hA hH hP.1 hBne
    inf_le_left hs inf_le_right
  by_contra hout
  exact Chapter3.no_common_normal_of_unique_maximal
    (T.isPGroup'.to_le (show baumann (T : Subgroup G) ≤ T from inf_le_left))
    (fun L hL hAL => Set.mem_singleton_iff.mp (hu ▸
      (show L ∈ maximalTwoLocalOvergroups A from ⟨hL,hAL⟩))) hout hc

theorem source_moved_reduced_minimalParabolic_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hP : IsMinimalParabolicOver T H)
    (U : Subgroup H) (hU : IsPReduced 2 U)
    (hj : ¬ elementaryAbelianMaxJ (T.subtype hH.2 : Subgroup H) ≤ centralizer (U : Set H)) :
    H ≤ M := by
  obtain ⟨B,hTB,hBH⟩ := hP.1.2.exists
  have hi := (intrinsic_minimalParabolic T H B hP hTB hBH).1
  have hsol := reduced_action_isSolvable
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hH U hU
  have hr := (Chapter3.sqtk_of_mem_H hG hH.1).stronglyQuasithin 3 (by decide) (by decide)
  have hs := (RankOneBaumann.SolvableSource.source_solvable_baumann_sylow_and_alpha
    (T.subtype hH.2) hi U hU hj hr hsol).1
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs
  have hb : (baumann (T.subtype hH.2 : Subgroup H)).map H.subtype =
      baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective
      (T.subtype hH.2 : Subgroup H)
    change (baumann (T.subtype hH.2 : Subgroup H)).map H.subtype =
      baumann ((T.subtype hH.2 : Subgroup H).map H.subtype) at he
    exact he.trans (congrArg baumann (map_subgroupOf_eq_of_le hH.2))
  rw [Subgroup.map_sup,hb] at hm
  exact source_minimalParabolic_le_of_baumann_sylow hG T hM hJ hH hP hm

/-- A.5.6 forbids an M-invariant span of a nontrivial Sylow-central seed across N ∩ M. -/
theorem source_no_invariant_span_of_ordering
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M N : Subgroup G} (hM : M ∈ maximalLocals T) (hN : N ∈ maximalLocals T)
    (hne : N ≠ M) (horder : OrderingLE T N M)
    (W : Subgroup G) (hW : W ≠ ⊥) (hWZ : W ≤ centralInvolutions T) :
    ¬ M ≤ normalizer (conjugateSpanBy W (N ⊓ M) : Set G) := by
  let D := conjugateSpanBy W (N ⊓ M)
  have hWD : W ≤ D := le_conjugateSpanBy _ _
  have hDne : D ≠ ⊥ := fun he => hW (bot_unique (hWD.trans he.le))
  have hDM : D ≤ localModule T M := conjugateSpanBy_mono hWZ inf_le_right
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  have htwo : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 (localModule T M)).to_le hDM
  have hd : D = conjugateSpanBy (D ⊓ centralOmega T) (N ⊓ M) := by
    apply le_antisymm
    · exact conjugateSpanBy_mono (le_inf hWD hWZ) le_rfl
    · exact conjugateSpanBy_le inf_le_left (le_normalizer_conjugateSpanBy _ _)
  intro hn
  have hNM : N ≤ M := le_of_generated_intersection hM.1 horder hDne htwo hd hn
  exact hne (le_antisymm hNM (hN.1.2 hM.1.1 hNM))

end CFSG.Quasithin.Chapter15.Section01
