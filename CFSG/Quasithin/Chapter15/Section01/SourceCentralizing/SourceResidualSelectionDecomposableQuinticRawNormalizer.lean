module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawThompson
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalClassification

/-!
# The original seed action on the literal component normalizer

Set R=N_S(L) and H=LR. The normal closure in H of the original central
involutions is reduced and is moved by L. Its centralizer quotient has
quasisimple generalized Fitting subgroup equal to the actual image of L.
The original Thompson normalizer bound gives a nontrivial offender, so
the proved B.5 classifier applies to this same action.

The result retains the literal seed, normalizer, quotient and action.
It assumes neither generation of M by its marked centralizer and T nor
a CaseI component record. It does not assert the later block catalogue.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The same raw component has a genuine reduced original-seed FF action
and the complete B.5 source conclusion on its actual offender subgroup. -/
theorem PreparedChosenModule.raw_component_normalizer_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hfit : generalizedFitting L = pCore 2 L)
    (houtMZ : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    let H := L ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    ∃ hr : IsPReduced 2 W,
      letI := hr.elementary
      let C := centralizer (W : Set H)
      let q := QuotientGroup.mk' C
      let K := (L.subgroupOf H).map q
      let ρ := NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      let J := offenderSubgroup ρ
      pCore 2 H = R.subgroupOf H ⊓ C ∧
        K = generalizedFitting (H ⧸ C) ∧ IsQuasisimple K ∧ IsFFModule ρ ∧
        K ≤ J ∧ Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          (ρ.comp J.subtype) (K.subgroupOf J)) := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let L0 := L.subgroupOf H
  let Z := (centralInvolutions T).subgroupOf H
  let W := normalClosure (Z : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  obtain ⟨_,_,hs,hJRS,hZR⟩ :=
    h.raw_component_thompson hG T hM hJ hu hZ hL hq hfit houtMZ houtM
  have hJS : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) :=
    (h.caseI_marked_thompson_control hG T hM hJ hZ).1
  let : L0.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer inf_le_right)
  have hL0 : L0.IsCComponent := hL.2.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let e : L0 ≃* L := subgroupOfEquivOfLe le_sup_left
  let := hq
  let : IsQuasisimple (L0 ⧸ pCore 2 L0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)]
  have hgen : L0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hZT : Z ≤ P := by
    rw [hPS]
    exact fun _ hz => hZR hz
  have hcent : Z ≤ centralizer (P : Set H) := by
    intro z hz x hx
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
      (show (x : G) ∈ (T : Subgroup G) from
        ((hP ▸ mem_map_of_mem H.subtype hx).1).1))
  have hcH : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    centralizer_pCore_sup_le 2 L R (hfit ▸ centralizer_generalizedFitting_le L)
      (T.isPGroup'.to_le (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left)))
      inf_le_right
  have hZC : Z ≤ centralizer (pCore 2 H : Set H) :=
    hcent.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
  have hWQ : W ≤ pCore 2 H := normalClosure_le_normal (hZC.trans hcH)
  have hWC : W ≤ centralizer (pCore 2 H : Set H) := normalClosure_le_normal hZC
  let : IsMulCommutative W :=
    le_centralizer_iff_isMulCommutative.mp (hWC.trans (centralizer_le hWQ))
  let : IsElementaryAbelian 2 (centralInvolutions T) := by
    change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G))
    infer_instance
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf (hZR.trans le_sup_right)
  let : IsMulCommutative (normalClosure (Z : Set H)) := inferInstanceAs (IsMulCommutative W)
  have hr : IsPReduced 2 W := isPReduced_normalClosure_of_sylow_central P Z hZT hcent
  let := hr.elementary
  have hmoved : ⁅W,L0⁆ ≠ ⊥ := by
    intro he
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    apply houtMZ
    refine le_inf hL.1 ?_
    intro l hl
    apply hMc.2
    intro z hz
    exact congrArg Subtype.val (hc (show (⟨l,mem_sup_left hl⟩ : H) ∈ L0 from hl)
      ⟨z,mem_sup_right (hZR hz)⟩ (le_normalClosure hz))
  have hnot : ¬L0 ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
    intro hn
    have hm := (map_mono (f := H.subtype) hn).trans
      ((elementaryAbelianMaxJ (P : Subgroup H)).le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS,hJS] at hm
    exact houtM (hm.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1)
  have hprod : ∀ x : H, ∃ l ∈ L0, ∃ t ∈ (P : Subgroup H), l*t=x := by
    intro x
    exact mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top x)
  obtain ⟨hcore,_,hfitK,hquasi⟩ := internalModule_quasisimple_core_structure
    W q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hr.quotient_pCore_eq_bot P L0 hL0 inferInstance hmoved hprod
  have hnotC : ¬elementaryAbelianMaxJ (P : Subgroup H) ≤ q.ker := by
    intro hh
    have hJP : elementaryAbelianMaxJ (P : Subgroup H) ≤ P := sSup_le fun _ hA => hA.1
    have hhC : elementaryAbelianMaxJ (P : Subgroup H) ≤ C := by
      simpa only [q,QuotientGroup.ker_mk'] using hh
    have hJQ : elementaryAbelianMaxJ (P : Subgroup H) ≤ pCore 2 H :=
      hcore.symm ▸ le_inf hJP hhC
    have he := elementaryAbelianMaxJ_eq_of_intermediate (P : Subgroup H) (pCore 2 H)
      hJQ (pCore_isPGroup.le_sylow_of_normal P)
    have hn : L0 ≤ normalizer (elementaryAbelianMaxJ (pCore 2 H) : Set H) :=
      le_normalizer_of_normal.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
    exact hnot (he ▸ hn)
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hff : IsFFModule ρ :=
    (ChapterB.lemma_B_2_7_local W q (QuotientGroup.mk'_surjective C)
      (QuotientGroup.ker_mk' C) P
      (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hnotC).1
  refine ⟨hr,hPS ▸ hcore,hfitK,hquasi,hff,?_⟩
  let K := L0.map q
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  let : IsQuasisimple K := hquasi
  have hcoreQ : pCore 2 (H ⧸ C) = ⊥ := hr.quotient_pCore_eq_bot
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  let : IsElementaryAbelian 2 A := hA.1.2
  have hshape : IsQuasisimple (generalizedFitting (H ⧸ C)) := hfitK ▸ hquasi
  have hf := generalizedFitting_normal_eq_of_quasisimple_or_three hcoreQ
    (Or.inl hshape) J A (IsElementaryAbelian.isPGroup 2 A) hA.1.1 (hA.le_offenderSubgroup ρ)
  have hKJ : K ≤ J := (hfitK.trans hf.symm).le.trans (map_subtype_le _)
  have hfitJ : generalizedFitting J = K.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hKJ,hf]
    exact hfitK.symm
  have hcoreJ : pCore 2 J = ⊥ := by
    apply ((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp
    apply le_bot_iff.mp
    have hm : (pCore 2 J).map J.subtype ≤ pCore 2 (H ⧸ C) :=
      le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map J.subtype⟩
    exact hm.trans hcoreQ.le
  let eK : K.subgroupOf J ≃* K := subgroupOfEquivOfLe hKJ
  let : IsQuasisimple (K.subgroupOf J) := IsQuasisimple.of_mulEquiv eK.symm
  let := h.elementary
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hsqL := (IsSQTK.equiv (subgroupOfEquivOfLe hL.1)).mp
    (hsq.subgroup (L.subgroupOf (centralizer (Z1 : Set G))))
  have hsqK : IsSQTK KnownSimple.IsKnownSimple K :=
    quasisimple_section_sqtk (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      ((IsSQTK.equiv e).mpr hsqL)
      (ChapterA.Section02.IsSectionOf.of_surjective (q.subgroupMap L0)
        (q.subgroupMap_surjective L0))
  have hyp : QuasisimpleSourceHypothesis (ρ.comp J.subtype) KnownSimple.IsKnownSimple
      (K.subgroupOf J) := by
    refine ⟨inferInstance,
      (NormalElementaryQuotient.representation_injective W q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)).comp J.subtype_injective,
      inferInstance,(IsSQTK.equiv eK).mpr hsqK,?_,hcoreJ,offenderSubgroup_restrict_eq_top ρ⟩
    rw [hfitJ]
    exact (sup_eq_left.mpr (by
      rw [←hfitJ]
      exact (show center J ≤ fittingSubgroup J from le_sSup ⟨inferInstance,inferInstance⟩).trans
        (fitting_le_generalizedFitting J))).symm
  exact ⟨hKJ,knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    ChapterB.SourceClassification.irreducibleClassification_knownSimple
    ChapterB.SourceInduction.nonbinaryG2RootPairInput _ _ _ _ hyp⟩

end CFSG.Quasithin.Chapter15.Section01
