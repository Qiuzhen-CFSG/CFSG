module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Containing

/-!
# A chosen module on the containing component's moved space

Thompson generation puts the faithful component into the offender subgroup
of the literal reduced-module quotient. When L₁≤K, the quotient above K is
a two-group. The B.5 classification then has only its quasisimple row.
A nonzero fixed vector forces the nonsplit Irr⁺ case, producing an actual
original chosen module on [R₂(KL₁T),K]. The unitary ReductionG consumer
constructs the fixed point and all local inputs from the source flag.
Source: Aschbacher--Smith B.5.1(2), B.5.6 and 13.3.14(g), pp.99,105,892--893.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterA.Section04 Noncentrality ChapterB.SourceInduction
open Chapter12.Section02 ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Thompson generation survives the literal local quotient and selects its component. -/
theorem component_join_offender_entry
    (T : Sylow 2 G) (J K : Subgroup G)
    (hJ : IsSQTK KnownSimple.IsKnownSimple J) (hKJ : K ≤ J)
    (hKN : J ≤ normalizer (K : Set G))
    (hK : (K.subgroupOf J).IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hfaith : intrinsicSignalizerModule K ≠ ⊥)
    (hTJ : (T : Subgroup G) ≤ J)
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K) :
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    (K.subgroupOf J).map q ≤ N ∧
      IsComponent N (((K.subgroupOf J).map q).subgroupOf N) ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative (ρ.comp N.subtype) := by
  let K₀ := K.subgroupOf J
  let S : Sylow 2 J := T.subtype hTJ
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hKN
  let eK : K₀ ≃* K := subgroupOfEquivOfLe hKJ
  have hq₀ : IsQuasisimple (K₀ ⧸ pCore 2 K₀) :=
    IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).symm
  have hfaith₀ : intrinsicSignalizerModule K₀ ≠ ⊥ := by
    intro hz
    apply hfaith
    have hm := intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective K₀
    rw [map_subgroupOf_eq_of_le hKJ,hz,Subgroup.map_bot] at hm
    exact hm
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup J)).map J.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTJ
  have hgen₀ : ⁅K₀,elementaryAbelianMaxJ (S : Subgroup J)⁆ = K₀ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKJ,hjmap,hgen]
  exact component_reduced_offender_entry hJ S K₀ hK hq₀ hfaith₀ hgen₀

private theorem containing_component_quasisimple_row
    (T : Sylow 2 G) (B A : Subgroup G)
    (hAB : A ≤ B) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hJ : IsSQTK KnownSimple.IsKnownSimple (Diagonal.localGroup B A T))
    (hK : (B.subgroupOf (Diagonal.localGroup B A T)).IsCComponent)
    (hqK : IsQuasisimple (B ⧸ pCore 2 B))
    (hfaith : intrinsicSignalizerModule B ≠ ⊥)
    (hgen : ⁅B,elementaryAbelianMaxJ (T : Subgroup G)⁆ = B) :
    let J := Diagonal.localGroup B A T
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
  let J := Diagonal.localGroup B A T
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
    (sup_le B.le_normalizer (hAB.trans B.le_normalizer)) hTB
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer hJN
  let : Bq.Normal := (inferInstance : BJ.Normal).map q (QuotientGroup.mk'_surjective C)
  let : B₀.Normal := inferInstance
  have hsup : BJ ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hTJ,
      ←MonoidHom.range_eq_map,range_subtype]
    change B ⊔ (T : Subgroup G) = (B ⊔ A) ⊔ (T : Subgroup G)
    rw [sup_eq_left.mpr hAB]
  have hquot : IsPGroup 2 ((J ⧸ C) ⧸ Bq) :=
    isPGroup_quotient_of_sup_eq_top Bq (((T : Subgroup G).subgroupOf J).map q)
      (T.isPGroup'.comap_subtype.map q) (by
        rw [←Subgroup.map_sup,hsup,map_top_of_surjective q (QuotientGroup.mk'_surjective C)])
  have hqN : IsPGroup 2 (N ⧸ B₀) := isPGroup_quotient_subgroupOf Bq N hquot
  obtain ⟨_,hcomp,hrows⟩ :=
    component_join_offender_entry T J B hJ hBJ hJN hK hqK hfaith hTJ hgen
  let : IsQuasisimple B₀ := hcomp.2
  have hcore : pCore 2 N = ⊥ := offenderSubgroup_twoCore ρ
    (isPReduced_reducedPSubgroup (p := 2) (G := J)).quotient_pCore_eq_bot
  exact ⟨generalizedFitting_eq_of_quasisimple_two_quotient B₀ hqN hcore,
    quasisimple_row_of_component_two_quotient (ρ.comp N.subtype) B₀ hcomp hqN hcore hrows⟩

/-- A containing point actor and a nonzero fixed moved section produce an
actual original chosen module on that section, using the full B.5 classification. -/
theorem containing_moved_module_chosen
    (T : Sylow 2 G) (B A : Subgroup G)
    (hAB : A ≤ B) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hJ : IsSQTK KnownSimple.IsKnownSimple (Diagonal.localGroup B A T))
    (hK : (B.subgroupOf (Diagonal.localGroup B A T)).IsCComponent)
    (hqK : IsQuasisimple (B ⧸ pCore 2 B))
    (hfaith : intrinsicSignalizerModule B ≠ ⊥)
    (hgen : ⁅B,elementaryAbelianMaxJ (T : Subgroup G)⁆ = B)
    (hfixedG : Diagonal.movedModule B A T ⊓ centralizer (B : Set G) ≠ ⊥) :
    Nonempty (ChosenModule T B
      (Diagonal.movedModule B A T)) := by
  let J := Diagonal.localGroup B A T
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
    (sup_le B.le_normalizer (hAB.trans B.le_normalizer)) hTB
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
  have himage : subspaceImage J I = Diagonal.movedModule B A T := by
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
    exact hfixedG hh
  obtain ⟨hBq,_,_⟩ :=
    component_join_offender_entry T J B hJ hBJ hJN hK hqK hfaith hTJ hgen
  obtain ⟨_,⟨c⟩⟩ :=
    containing_component_quasisimple_row T B A hAB hTB hJ hK hqK hfaith hgen
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
    change (B ⊔ A) ⊔ (T : Subgroup G) = _
    rw [sup_eq_left.mpr hAB]
  have aux : ∀ (J' : Subgroup G) (I' : Submodule (ZMod 2) (Additive (ReducedModule J'))),
      J' = B ⊔ (T : Subgroup G) →
      IsIrrPlusWith (reducedRepresentation J') (B.subgroupOf J')
        ((T : Subgroup G).subgroupOf J') I' →
      subspaceImage J' I' = Diagonal.movedModule B A T →
      Nonempty (ChosenModule T B (Diagonal.movedModule B A T)) := by
    intro J' I' hj' hi' he'
    subst J'
    exact ⟨⟨I',hi',he'⟩⟩
  exact aux J I hJ hchoice himage

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
