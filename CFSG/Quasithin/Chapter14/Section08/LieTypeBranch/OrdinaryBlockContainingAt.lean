module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBlockEntryAt
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Containing

/-!
# The containing-component branch with local recognition

When the point residual lies in the selected component, the original reduced
offender quotient modulo that component is a two-group. The proved B.5 row
sieve and the original nonzero fixed line then construct a ChosenModule on
the literal moved subgroup. Recognition is used only to escape at the same
G,T; every quotient and Sylow action is preserved.
Source: Aschbacher–Smith 13.3.14(g), pp.892–893, using B.5.1(2),B.5.6.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction ChapterB.QuasisimpleSource Chapter12.Section02
open Representation.BinaryOffender.Homogeneous
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

theorem ordinary_containing_component_quasisimple_row_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    let B₀ := ((B.subgroupOf J).map q).subgroupOf N
    generalizedFitting N = B₀ ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp N.subtype) B₀) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  let B₀ := Bq.subgroupOf N
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAK.trans B.le_normalizer)) (h1332 B hf).1
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  let : Bq.Normal := (inferInstance : BJ.Normal).map q (QuotientGroup.mk'_surjective C)
  let : B₀.Normal := inferInstance
  have hgen : BJ ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hTJ,
      ←MonoidHom.range_eq_map,range_subtype]
    change B ⊔ (T : Subgroup G) = (B ⊔ sourceOne L T P) ⊔ (T : Subgroup G)
    rw [sup_eq_left.mpr hAK]
  have hquot : IsPGroup 2 ((J ⧸ C) ⧸ Bq) :=
    isPGroup_quotient_of_sup_eq_top Bq (((T : Subgroup G).subgroupOf J).map q)
      (T.isPGroup'.comap_subtype.map q) (by
        rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective C)])
  have hqN : IsPGroup 2 (N ⧸ B₀) := isPGroup_quotient_subgroupOf Bq N hquot
  obtain ⟨_,hcomp,hrows⟩ :=
    ordinary_selected_offender_entry_of_original_source_at d hmax eL escape h1332 K hK hqK hf
  let : IsQuasisimple B₀ := hcomp.2
  have hcore : pCore 2 N = ⊥ := offenderSubgroup_twoCore ρ
    (isPReduced_reducedPSubgroup (p := 2) (G := J)).quotient_pCore_eq_bot
  exact ⟨generalizedFitting_eq_of_quasisimple_two_quotient B₀ hqN hcore,
    quasisimple_row_of_component_two_quotient (ρ.comp N.subtype) B₀ hcomp hqN hcore hrows⟩

theorem ordinary_containing_moved_module_chosen_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hAK : sourceOne L T P ≤ K.map H.subtype) :
    Nonempty (ChosenModule T (K.map H.subtype)
      (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  let Bq := BJ.map q
  let σ := reducedRepresentation J
  let I := moved σ BJ
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJN : J ≤ normalizer (B : Set G) := sup_le
    (sup_le B.le_normalizer (hAK.trans B.le_normalizer)) (h1332 B hf).1
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hact : σ = ρ.comp q := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) g w).symm
  have hI : I = moved ρ Bq := by
    change moved σ BJ = moved ρ (BJ.map q)
    rw [hact,moved_comp_map]
  have himage : subspaceImage J I = Diagonal.movedModule B (sourceOne L T P) T := by
    rw [hI]
    change subspaceImage J (subspaceCommutator ρ ⊤ (BJ.map q)) = _
    rw [←NormalElementaryQuotient.commutatorSpace_eq W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) BJ]
    change ((⁅W,BJ⁆.subgroupOf W).map W.subtype).map J.subtype = _
    rw [map_subgroupOf_eq_of_le (commutator_le_left W BJ),map_commutator,
      map_subgroupOf_eq_of_le hBJ]
    rfl
  have hfixed : I ⊓ fixedSpace σ BJ ≠ ⊥ := by
    intro he
    have hh := congrArg (ReducedNormal.subspaceImage J) he
    have heq : σ = ReducedNormal.representation J := by rfl
    rw [heq,ReducedNormal.subspaceImage_inf_fixedSpace J I B hBJ,
      ReducedNormal.subspaceImage_bot] at hh
    change subspaceImage J I ⊓ centralizer (B : Set G) = ⊥ at hh
    rw [himage] at hh
    exact ordinary_movedModule_fixed_ne_bot_of_actor_le d eL h1332 hc K hK hqK hf hAK hh
  obtain ⟨hBq,_,_⟩ :=
    ordinary_selected_offender_entry_of_original_source_at d hmax eL escape h1332 K hK hqK hf
  obtain ⟨_,⟨c⟩⟩ :=
    ordinary_containing_component_quasisimple_row_at d hmax eL escape h1332 K hK hqK hf hAK
  have hspace : c.sectionData.space.toSubmodule = moved ρ Bq := by
    rw [c.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hBq]
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace (ρ.comp N.subtype) (Bq.subgroupOf N)) := by
    rw [hspace,fixedSpace_subgroupOf ρ Bq N hBq]
    intro hh
    apply hfixed
    rw [hI,hact,fixedSpace_comp_map]
    exact hh.disjoint.eq_bot
  have hirr : IsIrrPlus ρ Bq (moved ρ Bq) := by
    rw [←hspace]
    exact (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp (c.clause_two hn).1
  have hirr' : IsIrrPlus σ BJ I := by
    have hh := IsIrrPlus.map_embedding σ ρ q (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)
      Function.injective_id (fun g w => by rw [hact]; rfl) BJ (moved ρ Bq) hirr
    simpa only [Submodule.map_id,←hI] using hh
  have hnormal : (T : Subgroup G).subgroupOf J ≤ normalizer (BJ : Set J) :=
    le_normalizer_of_normal
  have hstable : (T : Subgroup G).subgroupOf J ≤ subspaceStabilizer σ I :=
    subspaceCommutator_invariant_normalizer σ
      (by intro t ht v; simp) hnormal
  have hchoice : IsIrrPlusWith σ BJ ((T : Subgroup G).subgroupOf J) I := by
    refine ⟨hnormal,hirr'.choose,hirr',?_⟩
    apply le_antisymm
    · rw [orbitSpan_eq_self σ hstable]
      exact iSup_le fun S => iSup_le fun hS => hS.1
    · exact quotientImage_le_homogeneousPart σ hirr'.choose
  have hJ : J = B ⊔ (T : Subgroup G) := by
    change (B ⊔ sourceOne L T P) ⊔ (T : Subgroup G) = _
    rw [sup_eq_left.mpr hAK]
  have aux : ∀ (J' : Subgroup G) (I' : Submodule (ZMod 2) (Additive (ReducedModule J'))),
      J' = B ⊔ (T : Subgroup G) →
      IsIrrPlusWith (reducedRepresentation J') (B.subgroupOf J')
        ((T : Subgroup G).subgroupOf J') I' →
      subspaceImage J' I' = Diagonal.movedModule B (sourceOne L T P) T →
      Nonempty (ChosenModule T B (Diagonal.movedModule B (sourceOne L T P) T)) := by
    intro J' I' hj' hi' he'
    subst J'
    exact ⟨⟨I',hi',he'⟩⟩
  exact aux J I hJ hchoice himage

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
