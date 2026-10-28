module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.HeldOrder
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.GroupTheory.CComponent.SimplePairProduct
public import Theory.GroupTheory.CComponent.PairActionKernel
public import Theory.GroupTheory.PCoreInRestriction
public import Stellmacher.OmegaOneCenterMap

/-!
# The size of the actual nonnormal C.2.8 span

The two-conjugate orbit gives a product of the original simple two-core
quotients. The elementary center of the span's two-core contains the source
module, so the span acts nontrivially there and retains both odd ranks of
the seed. The small elementary automorphism calculation forces the two-core
to have order divisible by 64. This is the order obstruction used to finish
the Held covering row, without replacing the section-centralizer Sylow by
a full Sylow of the containing group.

Source: Aschbacher--Smith C.2.8, C.3.5 and C.4.5--8, pp.147,150,152--154,
applied in 4.4.6 and 10.2.3(2), pp.620,745.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.HypothesisC28
universe u v
variable {G : Type u} [Group G] [Finite G] {H M L R V : Subgroup G}
variable {κ : GroupClass.{u}}
private theorem span_odd_rank
    (h : HypothesisC28 κ H M L R V)
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ M ≤ normalizer (L : Set G))
    {D : Type v} [Group D] [Finite D] (f : M →* D)
    (hne : ((conjugateSpanBy L M).subgroupOf M).map f ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (((conjugateSpanBy L M).subgroupOf M).map f) =
      primeRank p (conjugateSpanBy L M) := by
  let A := L.subgroupOf M
  let X := conjugateSpanBy A (⊤ : Subgroup M)
  let Y := conjugateSpanBy L M
  have hYM : Y ≤ M := conjugateSpanBy_le_self h.component_le
  have hmap : X.map M.subtype = Y := by
    change (conjugateSpanBy A ⊤).map M.subtype = Y
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le h.component_le,
      ← MonoidHom.range_eq_map, range_subtype]
  have hX : X = Y.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hYM]
    exact hmap
  have hM : IsSQTK κ M :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.local_le)).mp (h.sqtk.subgroup (M.subgroupOf H))
  have hQ : IsSQTK κ (M ⧸ pCore 2 M) := by
    refine ⟨?_, hM.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hM.stronglyQuasithin p hp ho)
  have hi : (normalizer (A : Set M)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ h.component with hN | hi
    · let := hN
      apply (hn ?_).elim
      have hh := A.le_normalizer_map M.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, A,
        map_subgroupOf_eq_of_le h.component_le] using hh
    · exact hi
  let ae := subgroupOfEquivOfLe h.component_le
  let : IsSimpleGroup (A ⧸ pCore 2 A) :=
    (QuotientGroup.congr _ _ ae (pCore_map_iso 2 ae)).isSimpleGroup
  have hh := pair_span_action_odd_rank A h.component hi f (by change X.map f ≠ ⊥; rw [hX]; exact hne) ho
  change primeRank p (X.map f) = primeRank p X at hh
  rw [hX] at hh
  exact hh.trans (primeRank_congr p (subgroupOfEquivOfLe hYM))

/-- The literal quotient of the covering span is the product of its two simple seed quotients. -/
theorem simple_nonnormal_span_product_equiv
    (h : HypothesisC28 κ H M L R V)
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ M ≤ normalizer (L : Set G)) :
    Nonempty ((conjugateSpanBy L M ⧸ pCore 2 (conjugateSpanBy L M)) ≃*
      ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L))) := by
  let A := L.subgroupOf M
  have hM : IsSQTK κ M :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.local_le)).mp (h.sqtk.subgroup (M.subgroupOf H))
  have hQ : IsSQTK κ (M ⧸ pCore 2 M) := by
    refine ⟨?_, hM.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hM.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := fun ha => hn
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp ha)
  have hi := (Chapter1.Section02.proposition_1_2_1_three_orbit_source
    hQ h.component).resolve_left hnot
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  let tM : M := ⟨t,ht⟩
  have htnM : tM ∉ normalizer (A : Set M) := by
    rw [← subgroupOf_normalizer_eq h.component_le]
    exact htn
  let Y := conjugateSpanBy A (⊤ : Subgroup M)
  let B := A.map (MulAut.conj tM).toMonoidHom
  have hne : B ≠ A := fun he => htnM (mem_normalizer_iff_map_conj_eq.mpr he)
  have hp : A ⊔ B = Y := by
    apply le_antisymm
    · refine sup_le (le_conjugateSpanBy A ⊤) ?_
      change B ≤ conjugateSpanBy A ⊤
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun s : (⊤ : Subgroup M) => A.map (MulAut.conj (s : M)).toMonoidHom)
        ⟨tM,mem_top _⟩
    · change conjugateSpanBy A ⊤ ≤ A ⊔ B
      rw [conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro s
      rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hne (s : M) with he | he
      · exact he.le.trans le_sup_left
      · exact he.le.trans le_sup_right
  have hAY : A ≤ Y := hp ▸ le_sup_left
  have hBY : B ≤ Y := hp ▸ le_sup_right
  let a := (subgroupOfEquivOfLe hAY).trans (subgroupOfEquivOfLe h.component_le)
  let b := ((subgroupOfEquivOfLe hBY).trans ((MulAut.conj tM).subgroupMap A).symm).trans
    (subgroupOfEquivOfLe h.component_le)
  have hn' : A.subgroupOf Y ≠ B.subgroupOf Y := by
    intro he
    apply hne
    have hh := congrArg (map Y.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAY,map_subgroupOf_eq_of_le hBY] using hh.symm
  have hg : A.subgroupOf Y ⊔ B.subgroupOf Y = ⊤ := by
    rw [← subgroupOf_sup hAY hBY,hp,subgroupOf_self]
  obtain ⟨q,hq,hk,_,_⟩ := exists_twoCore_product_of_simple_pair
    (A.subgroupOf Y) (B.subgroupOf Y) (h.component.subgroupOf hAY)
    ((h.component.map_equiv (MulAut.conj tM)).subgroupOf hBY) hn' hg
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b))
  have hmap : Y.map M.subtype = conjugateSpanBy L M := by
    change (conjugateSpanBy A ⊤).map M.subtype = conjugateSpanBy L M
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le h.component_le,
      ← MonoidHom.range_eq_map,range_subtype]
  let aY : Y ≃* conjugateSpanBy L M :=
    (Subgroup.equivMapOfInjective Y M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨(QuotientGroup.congr _ _ aY.symm (pCore_map_iso 2 aY.symm)).trans
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq))⟩
/-- The source module lies in the characteristic elementary center of the span's two-core. -/
theorem elementary_core_layer (h : HypothesisC28 κ H M L R V) :
    ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ V ≤ W ∧
      W ≤ (conjugateSpanBy L M).pCoreIn 2 ∧ M ≤ normalizer (W : Set G) := by
  let X := conjugateSpanBy L M
  let C := X.pCoreIn 2
  let W := omegaOneCenterAmbient C
  have hMX : M ≤ normalizer (X : Set G) := le_normalizer_conjugateSpanBy L M
  have hMC : M ≤ normalizer (C : Set G) :=
    hMX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hVC : V ≤ C := le_pCoreIn_of_normalizes h.module_elementary.isPGroup h.module_le
    (le_normalizer_iff_commutator_le_left.mpr h.module_commutator.symm.le)
  have hCR : C ≤ R := by
    rw [← h.span_join_core]
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le X.le_normalizer (h.radical_le.trans hMX))
  let Z := (omega₁ (center C) (p := 2)).map (center C).subtype
  let : (omega₁ (center C) (p := 2)).Characteristic := omega₁_characteristic _
  let : Z.Characteristic := inferInstance
  refine ⟨W, omegaOneCenterAmbient_elementaryAbelian C, ?_, ?_,
    hMC.trans (normalizer_le_normalizer_characteristic_image C Z)⟩
  · intro x hx
    apply (mem_omegaOneCenterAmbient_iff C x).mpr
    refine ⟨hVC hx, ?_, ?_⟩
    · let := h.module_elementary
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    · intro c hc
      obtain ⟨v,hv,he⟩ := h.module_le_center_radical hx
      have hh := congrArg (fun y : R => (y : G)) ((mem_center_iff.mp hv) ⟨c,hCR hc⟩)
      change c * (v : G) = (v : G) * c at hh
      change (v : G) = x at he
      rwa [he] at hh
  · intro x hx
    exact ((mem_omegaOneCenterAmbient_iff C x).mp hx).1


/-- The original elementary layer retains both odd ranks of the simple seed. -/
theorem simple_nonnormal_elementary_layer_ranks
    (h : HypothesisC28 κ H M L R V)
    [IsSimpleGroup (L ⧸ pCore 2 L)] [Group.IsPerfect (L ⧸ pCore 2 L)]
    (hn : ¬ M ≤ normalizer (L : Set G)) :
    ∃ W : Subgroup G, IsElementaryAbelian 2 W ∧ V ≤ W ∧
      W ≤ (conjugateSpanBy L M).pCoreIn 2 ∧ M ≤ normalizer (W : Set G) ∧
      ∀ p : ℕ, p.Prime → Odd p →
        2 * primeRank p (L ⧸ pCore 2 L) ≤ primeRank p (MulAut W) := by
  obtain ⟨W,hWe,hVW,hWC,hMW⟩ := elementary_core_layer h
  let := hWe
  let X := conjugateSpanBy L M
  have hXM : X ≤ M := conjugateSpanBy_le_self h.component_le
  let f : M →* MulAut W := W.normalizerMonoidHom.comp (inclusion hMW)
  have hne : (X.subgroupOf M).map f ≠ ⊥ := by
    intro he
    have hk : X.subgroupOf M ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
    have hcomm : ⁅V,X⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro v hv x hx
      have hid : f ⟨x,hXM hx⟩ = 1 := hk hx
      have hfix := congrArg (fun a : MulAut W => (a ⟨v,hVW hv⟩ : G)) hid
      change x*v*x⁻¹ = v at hfix
      exact mul_inv_eq_iff_eq_mul.mp hfix
    exact h.module_nontrivial (h.module_commutator.trans hcomm)
  refine ⟨W,hWe,hVW,hWC,hMW,?_⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hr := span_odd_rank h hn f hne ho
  obtain ⟨a⟩ := simple_nonnormal_span_product_equiv h hn
  have he : primeRank p X = 2 * primeRank p (L ⧸ pCore 2 L) := by
    rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup,
      primeRank_congr p a,primeRank_prod_eq_add,two_mul]
  rw [←he,←hr]
  exact primeRank_subgroup_le _ _

/-- The actual covering span's two-core has order divisible by 64. -/
theorem simple_nonnormal_span_core_sixtyFour_dvd
    (h : HypothesisC28 κ H M L R V)
    [IsSimpleGroup (L ⧸ pCore 2 L)] [Group.IsPerfect (L ⧸ pCore 2 L)]
    (hn : ¬ M ≤ normalizer (L : Set G)) :
    2^6 ∣ Nat.card (pCore 2 (conjugateSpanBy L M)) := by
  obtain ⟨W,hWe,_,hWC,_,hr⟩ := simple_nonnormal_elementary_layer_ranks h hn
  let := hWe
  let X := conjugateSpanBy L M
  have hdW := elementary_sixtyFour_dvd_of_doubled_odd_ranks (L ⧸ pCore 2 L) W hr
  have hc : Nat.card W ∣ Nat.card (pCore 2 X) := by
    have hh := card_dvd_of_le hWC
    change Nat.card W ∣ Nat.card ((pCore 2 X).map X.subtype) at hh
    rwa [card_map_of_injective X.subtype_injective] at hh
  exact hdW.trans hc

end CFSG.Quasithin.ChapterC.HypothesisC28
