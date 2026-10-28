module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceComplete
public import CFSG.Quasithin.Chapter4.Section02.Unitary.SourceSetup

/-!
# Original-input pushing up for the remaining Baumann branch

The original reduced subgroup W embeds in Ω₁Z(O₂(LT)); its nonzero
commutator with L therefore proves that the full source module is nonzero.
Uniqueness over LT gives Hypothesis 4.1.1. Failure of uniqueness over L
then supplies a maximal pushing-up counterexample and every clause of
C.2.8, with its literal section-centralizer Sylow subgroup and conjugator.
No ChosenModule, ambient model exclusion or Chapter 13 context is needed.

Under Baumann escape, the already proved block-layer identity makes this
full module exactly [W,L]. This equality is proved through the characteristic
layer [O₂(L),L]; the original W is never identified with the source module.
The final theorem constructs the original A₅ counterexample still to be
excluded in the proof of 5.1.7(1). It does not assert uniqueness over L or
point-centralizer control. Those exclusions and final assembly remain with
the original-input Baumann task.

Source: Aschbacher--Smith 4.1.1--5, 4.2.4 and the opening of 4.3.2,
printed pp.605--608,613; application in 5.1.7(1), pp.633--634.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter4 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The actual normalizer and uniqueness over LT supply original 4.1.1. -/
theorem Input.original_pushingUp
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    Hypothesis411 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) L :=
  hypothesis411_of_normal_unique_sylow_join h.qtke
    ⟨h.maximal, sup_le L.le_normalizer h.sylow_normalizes,
      Chapter5.RankOneBaumannSource.unique_sylow_join h.qtke h.maximal_local
        h.sylow_normalizes⟩ le_rfl h.local_mem.2.2.1

/-- The original reduced W lies in the omega-one center of the actual local core. -/
theorem Input.reduced_le_original_omega
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    W ≤ omegaOneCenterAmbient ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let A := L ⊔ (T : Subgroup G)
  have hc : W ≤ A.pCoreIn 2 := by
    have hh := map_mono (f := A.subtype) h.reduced_internal.le_pCore
    rwa [map_subgroupOf_eq_of_le h.reduced.1] at hh
  have hz : W ≤ centralizer (A.pCoreIn 2 : Set G) := by
    have hh := (map_mono (f := A.subtype) h.reduced_internal.le_centralizer_pCore).trans
      (map_centralizer_le_centralizer_image (pCore 2 A) A.subtype)
    rwa [map_subgroupOf_eq_of_le h.reduced.1] at hh
  let := h.reduced.2.1
  intro w hw
  exact (mem_omegaOneCenterAmbient_iff _ w).mpr
    ⟨hc hw, elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw,
      fun q hq => hz hw q hq⟩

/-- The original moved subgroup embeds in the full source module; no equality with W is asserted. -/
theorem Input.moved_le_original_fullModule
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    ⁅W,L⁆ ≤ fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) :=
  commutator_mono h.reduced_le_original_omega le_rfl

/-- The same section-centralizer conjugator transports the local core and the original moved subgroup. -/
theorem Input.original_fullModule_comparison
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)) :
    ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      (⁅W,L⁆).map (MulAut.conj (c : G)).toMonoidHom ≤
        fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) := by
  let C := sectionCentralizerIn (normalizer (L : Set G)) L
  have hs := ChapterA.Section04.sylow_core_sectionCentralizer T L
    h.local_mem.2.2.1 h.sylow_normalizes
  rw [← sectionCentralizerIn_eq_twoSectionCentralizer] at hs
  obtain ⟨S0,hS0⟩ := hs
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq C S0 S
  have hmap : ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
      (S : Subgroup C).map C.subtype := by
    rw [← hS0,← hc]
    change ((S0 : Subgroup C).map C.subtype).map (MulAut.conj (c : G)).toMonoidHom =
      ((S0 : Subgroup C).map (MulAut.conj c).toMonoidHom).map C.subtype
    rw [map_map,map_map]
    rfl
  have hLc : L.map (MulAut.conj (c : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp c.property.1
  refine ⟨c,hmap,?_⟩
  have hv := map_mono (f := (MulAut.conj (c : G)).toMonoidHom)
    h.moved_le_original_fullModule
  rwa [fullModule_map,hLc,hmap] at hv

/-- Noncentrality of the original W makes every marked source full module nontrivial. -/
theorem Input.original_fullModule_ne_bot
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)) :
    fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) ≠ ⊥ := by
  obtain ⟨c,_,hc⟩ := h.original_fullModule_comparison S
  intro he
  exact h.noncentral ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj (c : G)).injective).mp
    (bot_unique (hc.trans_eq he)))

omit [Finite G] in
private theorem core_join_of_sectionSylow {A R : Subgroup G}
    (hLA : L ≤ A) (hn : (L.subgroupOf A).Normal) (hp : IsPPerfect 2 L)
    (hs : ∃ S : Sylow 2 (sectionCentralizerIn A L),
      (S : Subgroup (sectionCentralizerIn A L)).map (sectionCentralizerIn A L).subtype = R) :
    (L ⊔ R).pCoreIn 2 = R := by
  have hs' : ∃ S : Sylow 2 (ChapterA.Section04.twoSectionCentralizer L A),
      (S : Subgroup (ChapterA.Section04.twoSectionCentralizer L A)).map
        (ChapterA.Section04.twoSectionCentralizer L A).subtype = R := by
    rwa [← sectionCentralizerIn_eq_twoSectionCentralizer]
  have hm := (ChapterA.Section04.isMaximalTwoSignalizer_iff _ _ _).mp
    ((ChapterA.Section04.maximal_signalizer_iff_sylow L A R hLA hn.isSubnormal hp).mpr hs')
  have hR : R ≤ (L ⊔ R).pCoreIn 2 := le_pCoreIn_of_normalizes hm.1.isPGroup le_sup_right
    (sup_le hm.1.normalizes R.le_normalizer)
  refine le_antisymm (hm.2 _ ((ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr ?_) hR) hR
  exact ⟨(pCoreIn_le 2 _).trans (sup_le hLA hm.1.le),isPGroup_pCoreIn 2 _,
    le_sup_left.trans ((L ⊔ R).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))⟩

/-- A maximal source counterexample containing L supplies all clauses of C.2.8 on that same L. -/
theorem Input.original_C28_of_muStar
    (h : Input KnownSimple.IsKnownSimple T L W n)
    {Mminus J H : Subgroup G}
    (hminus : Mminus ∈ sigma (normalizer (L : Set G)) L)
    (hJ : J ∈ muStar (normalizer (L : Set G)) L Mminus)
    (hLJ : L ≤ J) (hH : IsMaximalTwoLocal H) (hJH : J ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set G))
    (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRS : J.pCoreIn 2 ≤ (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
      L (J.pCoreIn 2)
      (fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) := by
  let M := normalizer (L : Set G)
  let A := H ⊓ M
  let R := J.pCoreIn 2
  let Q := (S : Subgroup (sectionCentralizerIn M L)).map (sectionCentralizerIn M L).subtype
  let U := fullModule L Q
  have hyp := h.original_pushingUp
  have hmem := Chapter1.mem_H_of_isTwoLocal hH.1
  have hLA : L ≤ A := le_inf (hLJ.trans hJH) L.le_normalizer
  have hn : (L.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  have hres : (pResidual 2 (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype = L := by
    rw [inf_eq_left.mpr (hLJ.trans hJH),(pResidual_eq_top_iff 2 L).mpr h.local_mem.2.2.1,
      ← MonoidHom.range_eq_map,range_subtype]
  have hs := (lemma_4_1_4_4 hyp hminus hJ hmem hJH hout).1
  rw [hres] at hs
  have hdata := fullModule_data hyp.plus_perfect
    (sectionSylow_normalized hyp.plus_le hyp.plus_normal hyp.plus_perfect S)
  have hUne := h.original_fullModule_ne_bot S
  have hUc := lemma_4_1_5_1 hyp hminus hJ S hRS hdata.1
  have hUL := lemma_4_1_5_3 hyp hJ.1.1 hJH S hdata.1 hdata.2.2
  rw [hres] at hUL
  have hRA : R ≤ A := (pCoreIn_le 2 J).trans
    (le_inf hJH (hJ.1.1.1.trans hminus.1))
  have hUA : U ≤ A := hUc.trans ((map_subtype_le _).trans hRA)
  have hULe : U ≤ L := by
    change U = ⁅U,L⁆ at hUL
    rw [hUL]
    exact le_normalizer_iff_commutator_le_right.mp (hUA.trans inf_le_right)
  have hspan : conjugateSpanBy L A = L := le_antisymm
    (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy L A)
  have hcore := core_join_of_sectionSylow hLA hn hyp.plus_perfect hs
  have hNU := lemma_4_1_5_2 hyp S hUne hdata.1 rfl
  let := h.quotient_quasisimple
  have hcover : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right L (L.pCoreIn 2)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))),
      sup_eq_left.mpr (pCoreIn_le 2 L)]
  refine
    { sqtk := h.qtke.twoLocal_sqtk hH.1
      radical_isTwoGroup := isPGroup_pCoreIn 2 J
      radical_le := hRA
      local_le := inf_le_left
      local_fitting := lemma_4_1_4_6 hyp hminus hJ hmem hJH hout
      core_nontrivial := hmem
      component_le := hLA
      component := normal_cover_isCComponent hLA le_rfl hn hyp.plus_perfect hcover
      section_sylow := ?_
      characteristic_control := ?_
      module_nontrivial := hUne
      module_elementary := hdata.2.1
      module_le := ?_
      module_commutator := ?_
      module_central := ?_
      module_normalizer := le_inf inf_le_left (inf_le_right.trans hNU) }
  · change ∃ S' : Sylow 2 (ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy L A) A), _
    rw [hspan,← sectionCentralizerIn_eq_twoSectionCentralizer]
    exact hs
  · have hc := characteristicNormalizerClosure_subgroupOf_le (hRA.trans inf_le_left)
      (lemma_4_1_4_2 hyp hminus hJ)
    intro x hx
    exact ⟨x.property,hc hx⟩
  · change U ≤ conjugateSpanBy L A
    rwa [hspan]
  · change U = ⁅U,conjugateSpanBy L A⁆
    rwa [hspan]
  · change U ≤ (center ((conjugateSpanBy L A ⊔ R).pCoreIn 2)).map _
    rw [hspan,hcore]
    exact hUc

/-- The original nonzero moved subgroup is a normal two-subgroup of L. -/
theorem Input.original_core_ne_bot
    (h : Input KnownSimple.IsKnownSimple T L W n) : L.pCoreIn 2 ≠ ⊥ := by
  have hmoveL : ⁅W,L⁆ ≤ L := le_normalizer_iff_commutator_le_right.mp
    (h.reduced.1.trans (sup_le L.le_normalizer h.sylow_normalizes))
  have hmoveCore : ⁅W,L⁆ ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    h.commutator_reduced.2.1.isPGroup hmoveL
    (le_sup_left.trans (reduced_normalizes h.commutator_reduced))
  exact fun he => h.noncentral (bot_unique (hmoveCore.trans_eq he))

/-- Failure of uniqueness over L constructs the actual maximal counterexample and full-module marking. -/
theorem Input.original_source_C28_of_not_unique
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L L) ∧
      L ≤ J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ H ⊓ normalizer (L : Set G) < H ∧
      J.pCoreIn 2 ≤ (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        L (J.pCoreIn 2)
        (fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        (⁅W,L⁆).map (MulAut.conj (c : G)).toMonoidHom ≤
          fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) := by
  have hcover : (L : Set G) ⊆ (L : Set G) * (L.pCoreIn 2 : Set G) := by
    intro x hx
    exact ⟨x,hx,1,one_mem _,mul_one x⟩
  obtain ⟨hs,_⟩ := coveringOvergroup_eta L.le_normalizer le_rfl L.le_normalizer
    hcover h.original_core_ne_bot
  obtain ⟨J,H,hJ,hLJ,hH,hJH,hout,_⟩ := maximal_counterexample_of_component_cover
    h.qtke h.maximal L.le_normalizer le_rfl L.le_normalizer hcover h.original_core_ne_bot hnot
  have hLJ' : L ≤ J := fun x hx => (hLJ.2 ⟨hx,hx⟩).1
  have hyp := h.original_pushingUp
  have hJC := core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hs.1 hJ.1.1
  let C := sectionCentralizerIn (normalizer (L : Set G)) L
  obtain ⟨S,hRS⟩ := ((isPGroup_pCoreIn 2 J).comap_subtype :
    IsPGroup 2 ((J.pCoreIn 2).subgroupOf C)).exists_le_sylow
  have hRS' : J.pCoreIn 2 ≤ (S : Subgroup C).map C.subtype := by
    intro x hx
    exact ⟨⟨x,hJC hx⟩,hRS hx,rfl⟩
  exact ⟨J,H,S,hJ,hLJ',hH,hJH,hout,
    lt_of_le_not_ge inf_le_left (fun he => hout (he.trans inf_le_right)),hRS',
    h.original_C28_of_muStar hs hJ hLJ' hH hJH hout S hRS',
    h.original_fullModule_comparison S⟩

private theorem fullModule_le_block_layer
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)) :
    fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) ≤
      (ChapterC.blockU L).map L.subtype := by
  let Q := (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
    (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
  let U := fullModule L Q
  have hyp := h.original_pushingUp
  have hd := fullModule_data hyp.plus_perfect
    (sectionSylow_normalized hyp.plus_le hyp.plus_normal hyp.plus_perfect S)
  have ho : omegaOneCenterAmbient Q ≤ normalizer (L : Set G) := by
    intro x hx
    exact ((map_subtype_le _).trans inf_le_left)
      ((mem_omegaOneCenterAmbient_iff Q x).mp hx).1
  have hUL : U ≤ L := le_normalizer_iff_commutator_le_right.mp ho
  have hUcore : U ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes hd.2.1.isPGroup hUL
    (le_normalizer_iff_commutator_le_left.mpr hd.2.2.ge)
  have hb : (ChapterC.blockU L).map L.subtype = ⁅L.pCoreIn 2,L⁆ := by
    rw [ChapterC.blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    rfl
  rw [hb,hd.2.2]
  exact commutator_mono hUcore le_rfl

/-- Baumann escape identifies the full module with [W,L] through the characteristic block layer. -/
theorem Input.original_fullModule_eq_moved_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)) :
    fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) = ⁅W,L⁆ := by
  have hb := (h.alternating_block_of_baumann_escape hout).2.2.1
  obtain ⟨c,_,hc⟩ := h.original_fullModule_comparison S
  have hn : normalizer (L : Set G) ≤ normalizer ((⁅W,L⁆ : Subgroup G) : Set G) := by
    rw [← hb]
    exact normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)
  have he := mem_normalizer_iff_map_conj_eq.mp (hn c.property.1)
  change (⁅W,L⁆).map (MulAut.conj (c : G)).toMonoidHom = ⁅W,L⁆ at he
  rw [he] at hc
  exact le_antisymm ((fullModule_le_block_layer h S).trans_eq hb) hc

/-- The remaining original Baumann branch supplies a genuine A₅ C.2.8 counterexample, without an extra source premise. -/
theorem Input.original_a5_counterexample_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ChapterC.IsAlternatingBlock L 5 ∧ (ChapterC.blockU L).map L.subtype = ⁅W,L⁆ ∧
    ∃ J H : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L L) ∧
      L ≤ J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ H ⊓ normalizer (L : Set G) < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        L (J.pCoreIn 2) ⁅W,L⁆ := by
  have hb := h.alternating_block_of_baumann_escape hout
  obtain ⟨J,H,S,hJ,hLJ,hH,hJH,ho,hlt,_,hC,_⟩ :=
    h.original_source_C28_of_not_unique
      (fun hu => hout (h.baumann_normalizer_of_source_uniqueness hu.2.2))
  rw [h.original_fullModule_eq_moved_of_baumann_escape hout S] at hC
  exact ⟨hb.2.1,hb.2.2.1,J,H,hJ,hLJ,hH,hJH,ho,hlt,hC⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
