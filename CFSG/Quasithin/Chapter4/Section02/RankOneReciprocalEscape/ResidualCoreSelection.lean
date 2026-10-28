module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Selection
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SectionKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ClosureSylow
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupAction.SubgroupConjugation

/-!
# Selecting the involution-centralizer overgroup in pushing up

Replace the maximal counterexample J by F O₂(J), where F = (L ∩ H)∞.
The two-core is unchanged, and the original intersection with L is retained,
so the source maximality relation survives. The nontrivial O₂(H) centralizes
every ordinary component of H. The two-group O₂(J) fixes an involution in
O₂(H), so the replacement and the entire original component lie in its
centralizer. Select an outside maximal two-local over this full centralizer
and reconstruct all C.2.8 data there, keeping the original chosen module.

Containment of the old component in the selected overgroup is proved here;
its component status in that overgroup requires a further comparison.
No local normality is silently promoted to ambient normality.
Source: Aschbacher--Smith, 4.2.13, printed pp.611--612, using 4.1.4--5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

/-- Replace the original counterexample by its intersection residual and its
unchanged two-core. Both entries of the source maximality relation survive. -/
theorem residual_core_selection {T : Sylow 2 G} {L V A J H W : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (_D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hw : Witness L V A J H W) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let I := F ⊔ J.pCoreIn 2
    I.pCoreIn 2 = J.pCoreIn 2 ∧
      PushLE L J I ∧ I ≤ H ∧
      I ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) := by
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,he,hrest⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let I := F ⊔ R
  let M := normalizer (L : Set G)
  let Mminus := coveringOvergroup M L (oddActorResidual L A)
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hRH : R ≤ H := (pCoreIn_le 2 J).trans hJH
  have hRM : R ≤ M := hc.radical_le.trans inf_le_right
  have hIH : I ≤ H := sup_le hFH hRH
  have hn : H ⊓ M ≤ normalizer (F : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hN
  have hspan : conjugateSpanBy F (H ⊓ M) = F :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hcore : I.pCoreIn 2 = R := by
    have hh := hc.span_join_core
    rwa [hspan] at hh
  have hMminus : Mminus = L ⊔ sectionCentralizerIn M L := by
    apply le_antisymm
    · exact sup_le (((oddActorResidual_le L A).trans inf_le_left).trans le_sup_left) le_sup_right
    · refine sup_le ?_ le_sup_right
      intro l hl
      obtain ⟨j,hj,q,hq,rfl⟩ := hJ.1.1.2.2.1 hl
      exact mul_mem (hJ.1.1.1 hj)
        (show q ∈ Mminus from (show sectionCentralizerIn M L ≤ Mminus from le_sup_right) (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hs : Mminus ∈ sigma M L := by
    rw [hMminus]
    exact ⟨sup_le L.le_normalizer inf_le_left,le_rfl⟩
  have hbounds := lemma_4_1_4_5 (source_hypothesis411 h hM) hs hJ
    (Chapter1.mem_H_of_isTwoLocal hH.1) hJH
    (fun hh => hstrict.ne (inf_eq_left.mpr hh))
  have hQ : L.pCoreIn 2 ⊓ (H ⊓ M) ≤ (H ⊓ M).pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 L).to_le inf_le_left) inf_le_right
    exact (le_inf (inf_le_right.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
      (H ⊓ M).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hJI : J ⊓ L ≤ I := by
    intro j hj
    obtain ⟨f,hf,q,hq,heq⟩ := hcover ▸ (show j ∈ (L : Set G) from hj.2)
    have hqH : q ∈ H := by
      have ht := H.mul_mem (H.inv_mem (hFH hf)) (hJH hj.1)
      rwa [←heq,inv_mul_cancel_left] at ht
    have hqR : q ∈ R := hbounds.2.2.2 (hQ ⟨hq,hqH,L.le_normalizer (pCoreIn_le 2 L hq)⟩)
    rw [←heq]
    exact mul_mem_sup hf hqR
  have hrel : PushLE L J I := ⟨hcore.symm.le,le_inf hJI inf_le_right⟩
  have hIM : I ≤ M := sup_le (hFL.trans L.le_normalizer) hRM
  have hcov : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G) := by
    intro l hl
    obtain ⟨f,hf,q,hq,rfl⟩ := hcover ▸ hl
    exact ⟨f,(show F ≤ I from le_sup_left) hf,q,hq,rfl⟩
  have hne : I.pCoreIn 2 ≠ ⊥ := hcore ▸ hc.radical_ne_bot
  obtain ⟨_,heta⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hIM hcov hne
  have hminusI : coveringOvergroup M L I = Mminus := by
    rw [hMminus]
    apply le_antisymm
    · exact sup_le (sup_le (hFL.trans le_sup_left)
        ((core_le_sectionCentralizer_of_eta L.le_normalizer
          (source_hypothesis411 h hM).plus_normal
          (source_hypothesis411 h hM).plus_perfect hs.1 hJ.1.1).trans le_sup_right)) le_sup_right
    · exact (coveringOvergroup_eta L.le_normalizer le_rfl hIM hcov hne).1.2
  rw [hminusI] at heta
  refine ⟨hcore,hrel,hIH,⟨⟨heta,⟨H,⟨Chapter1.mem_H_of_isTwoLocal hH.1,hIH⟩,?_⟩⟩,?_⟩⟩
  · exact fun hh => hstrict.ne (inf_eq_left.mpr hh)
  · intro B hB hIB hlt
    apply hJ.2 B hB (hrel.trans hIB)
    change I.pCoreIn 2 < B.pCoreIn 2 at hlt
    rwa [hcore] at hlt


private theorem fixed_involution_in_core (H R : Subgroup G)
    (hR : IsPGroup 2 R) (hRH : R ≤ H) (hne : H.pCoreIn 2 ≠ ⊥) :
    ∃ r : G, r ∈ H.pCoreIn 2 ∧ orderOf r = 2 ∧ R ≤ centralizer ({r} : Set G) := by
  let Q := H.pCoreIn 2
  have hRQ : R ≤ normalizer (Q : Set G) := hRH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  let _ := conjMulDistribMulActionOfLeNormalizer R Q hRQ
  let B := FixedPoints.subgroup R Q
  have hd : 2 ∣ Nat.card Q := (isPGroup_pCoreIn 2 H).card_eq_or_dvd.resolve_left
    (fun hc => hne (Subgroup.card_eq_one.mp hc))
  have hm := hR.card_modEq_card_fixedPoints Q
  change Nat.card Q % 2 = Nat.card B % 2 at hm
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G := B) 2
    (Nat.dvd_of_mod_eq_zero (hm.symm.trans (Nat.mod_eq_zero_of_dvd hd)))
  refine ⟨r.val.val,r.val.property,?_,?_⟩
  · exact (orderOf_coe r.val).trans ((orderOf_coe r).trans hr)
  · intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg Subtype.val (r.property (⟨x,hx⟩ : R))
    change x * r.val.val * x⁻¹ = r.val.val at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- The source involution belongs to the original ambient two-core. It fixes
the same full covering component and the residual-core replacement. -/
theorem residual_core_involution {L V A J H W : Subgroup G}
    (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    :
    ∃ r : G, r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
      K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) := by
  have hc := hw.2.2.2.2.2.2.1
  obtain ⟨r,hr,ho,hR⟩ := fixed_involution_in_core H (J.pCoreIn 2)
    (isPGroup_pCoreIn 2 J) ((pCoreIn_le 2 J).trans hw.2.2.2.1) hc.core_nontrivial
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hcent := hK.le_centralizer_of_solvable_normal (pCore 2 H)
  refine ⟨r,hr,hc.ambient_core_le_radical hr,ho,sup_le ?_ hR⟩
  rintro k ⟨k,hk,rfl⟩
  obtain ⟨q,hq,hqr⟩ := hr
  subst r
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((hcent hk) q hq)).symm

/-- Reselect an outside maximal two-local over the full centralizer of an
involution in the original core. The original full component is contained
in the new overgroup, but its promotion to a component there is not assumed. -/
theorem residual_core_centralizer_overgroup
    {T : Sylow 2 G} {L V A J H W : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let I := F ⊔ J.pCoreIn 2
    I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
      I ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
      ∃ (r : G) (H' : Subgroup G),
        r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
        K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
        IsMaximalTwoLocal H' ∧ centralizer ({r} : Set G) ≤ H' ∧
        I ≤ H' ∧ K.map H.subtype ≤ H' ∧ ¬ H' ≤ normalizer (L : Set G) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFKg : F ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  obtain ⟨hcore,hpush,hIH,hI⟩ := residual_core_selection h D hM hw
  obtain ⟨r,hr,hRr,ho,hCr⟩ := residual_core_involution hw K hK
  have hlocal : IsTwoLocal (centralizer ({r} : Set G)) := by
    refine ⟨zpowers r,?_,?_,(normalizer_zpowers_eq_centralizer_of_order_two r ho).symm⟩
    · intro hb
      have he := mem_zpowers r
      rw [hb,mem_bot] at he
      rw [he,orderOf_one] at ho
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ho,pow_one])
  obtain ⟨H',hH',hCH'⟩ :=
    exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot (centralizer ({r} : Set G)) (by
      intro hb
      exact (Chapter1.mem_H_of_isTwoLocal hlocal)
        (by simp only [pCoreIn,hb,Subgroup.map_bot]))
  have hKH' : K.map H.subtype ≤ H' := le_sup_left.trans (hCr.trans hCH')
  refine ⟨hcore,hpush,hI,r,H',hr,hRr,ho,hCr,hH',hCH',?_,hKH',?_⟩
  · exact (sup_le_sup_right hFKg _).trans (hCr.trans hCH')
  · intro hm
    apply hout
    intro k hk
    exact ⟨k.property,hm (hKH' (mem_map_of_mem H.subtype hk))⟩


/-- Rebuild the genuine C.2.8 witness on the selected outside overgroup.
The original chosen module and actual quotient map are retained. -/
theorem witness_on_selected_overgroup
    {T : Sylow 2 G} {L V A J H W I H' : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hw : Witness L V A J H W)
    (hpush : PushLE L J I)
    (hI : I ∈ muStar (normalizer (L : Set G)) L
      (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)))
    (hH' : IsMaximalTwoLocal H') (hIH' : I ≤ H')
    (hout : ¬ H' ≤ normalizer (L : Set G)) :
    ∃ W' : Subgroup G, Witness L V A I H' W' := by
  have hFL : oddActorResidual L A ≤ L := (oddActorResidual_le L A).trans inf_le_left
  have hsigma : coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A) ∈
      sigma (normalizer (L : Set G)) L := by
    refine ⟨sup_le (hFL.trans L.le_normalizer) inf_le_left,sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact mul_mem (hw.1.1.1.1 hj)
      ((show sectionCentralizerIn (normalizer (L : Set G)) L ≤
        coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A) from le_sup_right)
        (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hyp := source_hypothesis411 h hM
  have hIC := core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hsigma.1 hI.1.1
  let C := sectionCentralizerIn (normalizer (L : Set G)) L
  obtain ⟨S,hRS⟩ := ((isPGroup_pCoreIn 2 I).comap_subtype :
    IsPGroup 2 ((I.pCoreIn 2).subgroupOf C)).exists_le_sylow
  have hRS' : I.pCoreIn 2 ≤ (S : Subgroup C).map C.subtype := by
    intro i hi
    exact ⟨⟨i,hIC hi⟩,hRS hi,rfl⟩
  have hc := Unitary.source_C28_of_muStar h D hM hsigma hI hH' hIH' hout S hRS'
  obtain ⟨c,hmark,hVW⟩ := Unitary.exists_fullModule_comparison h D hM S
  have hVI := hw.2.2.2.2.2.1.trans hpush.1
  have hr := chosen_intersection_twoResidual_eq_solvableResidual h hI.1.1.2.2.1 hIH'
  have hd := chosen_oddActorResidual_counterexample_residual h D hI.1.1.2.2.1 hIH' hVI
  rw [hr] at hd
  obtain ⟨e,he⟩ := exists_pCoreQuotientEquiv_of_cover
    ((map_subtype_le _).trans inf_le_left) hd.1.subset
  have hsize := card_le_of_le hVW
  rw [card_map_of_injective (MulAut.conj (c : G)).injective] at hsize
  exact ⟨_,hI,hw.2.1.trans hpush,hH',hIH',
    lt_of_le_not_ge inf_le_left (fun he => hout (he.trans inf_le_right)),hVI,hc,
    hd.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2,⟨e,he⟩,
    hc.oddCore_eq_bot,hc.isRadical,hc.sylow_in_normalClosure,hc.section_fitting_eq_core,
    hc.section_sylow_in_H,hsize,c,hVW⟩

/-- Full involution-centralizer reselection, retaining the original covering
component, and constructing all source hypotheses on the new overgroup. -/
theorem selected_involution_witness
    {T : Sylow 2 G} {L V A J H W : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map
      (L ⊓ H).subtype).subgroupOf H ≤ K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let I := F ⊔ J.pCoreIn 2
    I.pCoreIn 2 = J.pCoreIn 2 ∧ PushLE L J I ∧
      ∃ (r : G) (H' W' : Subgroup G),
        r ∈ H.pCoreIn 2 ∧ r ∈ J.pCoreIn 2 ∧ orderOf r = 2 ∧
        K.map H.subtype ⊔ J.pCoreIn 2 ≤ centralizer ({r} : Set G) ∧
        centralizer ({r} : Set G) ≤ H' ∧ K.map H.subtype ≤ H' ∧
        Witness L V A I H' W' := by
  obtain ⟨hcore,hpush,hI,r,H',hr,hRr,ho,hCr,hH',hCH',hIH',hKH',hout'⟩ :=
    residual_core_centralizer_overgroup h D hM hw K hK hFK hout
  obtain ⟨W',hW'⟩ := witness_on_selected_overgroup h D hM hw hpush hI hH' hIH' hout'
  exact ⟨hcore,hpush,r,H',W',hr,hRr,ho,hCr,hCH',hKH',hW'⟩

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
