module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisRadicalLift
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.RudvalisThompson
/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.RudvalisRadicalLift`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 Stellmacher
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original radical intersection is the full module preimage; its
normalizer image is the full module-image normalizer. -/
theorem unitary_original_pushingUp_rudvalis_radical_normalizer (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let U := (W.subgroupOf H).subgroupOf K
    let E := U.map f
    let P := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    P.map f = E ∧ P = U ⊔ center K ∧ normalizer (E : Set Rudvalis.Model) = C := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let U := (W.subgroupOf H).subgroupOf K
  let E := U.map f
  let P := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  let C := C0.map f
  change P.map f = E ∧ P = U ⊔ center K ∧ normalizer (E : Set Rudvalis.Model) = C
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  have hi (a : MulAut K) : a ∈ MulAut.innerSubgroup K := by
    rw [←MulAut.comap_inner_centralQuotientAction e]
    exact Rudvalis.component_conj_surjective (MulAut.centralQuotientAction e a)
  have hNP : normalizer (P : Set K) ≤ C0 :=
    hc.ordinary_radical_normalizer_le_local_of_inner K hK hi
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)
  have hp := hc.ordinary_radical_intersection_isRadical K hK
  have hZP : f.ker ≤ P := by
    rw [hk,hz]
    exact pCore_le_of_pCore_normalizer_le P hp.isPGroup hp.2.le
  obtain ⟨_,hcore,hcent⟩ := unitary_original_pushingUp_rudvalis_normalizer
    s hcover hJH hc K hK e c hVW
  change C.pCoreIn 2 = E at hcore
  change C ⊓ centralizer (E : Set Rudvalis.Model) = E at hcent
  have hUP : U ≤ P := subgroupOf_mono K (subgroupOf_mono H
    (hc.module_le_center_radical.trans (map_subtype_le _)))
  have hPE : P.map f = E := by
    apply le_antisymm _ (map_mono hUP)
    rintro _ ⟨r,hr,rfl⟩
    apply hcent.le
    refine ⟨mem_map_of_mem f (hc.radical_le hr),?_⟩
    rintro _ ⟨u,hu,rfl⟩
    have hh : u*r = r*u := by
      apply K.subtype_injective
      apply H.subtype_injective
      obtain ⟨w,hw,he⟩ := hc.module_le_center_radical hu
      have hh := congrArg (J.pCoreIn 2).subtype
        (mem_center_iff.mp hw (⟨(r : G),hr⟩ : J.pCoreIn 2))
      change (r : G)*(w : G) = (w : G)*(r : G) at hh
      change (w : G) = (u : G) at he
      rw [he] at hh
      exact hh.symm
    simpa only [map_mul] using congrArg f hh
  have hP : P = U ⊔ center K := by
    have he := congrArg (comap f) hPE
    rw [comap_map_eq_self hZP,comap_map_eq,hk] at he
    exact he
  have hN : (normalizer (P : Set K)).map f = normalizer (E : Set Rudvalis.Model) := by
    have he : (normalizer (P.map f : Set Rudvalis.Model)).comap f =
        normalizer (P : Set K) := by
      rw [comap_normalizer_eq_of_surjective _ hf,comap_map_eq_self hZP]
    rw [←he,map_comap_eq_self_of_surjective hf,hPE]
  refine ⟨hPE,hP,le_antisymm ?_ ?_⟩
  · rw [←hN]
    exact map_mono hNP
  · rw [←hcore]
    exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))

/-- The exact source normalizer and point orders, with the central kernel discharged. -/
theorem unitary_original_pushingUp_rudvalis_exact_sizes (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    normalizer (E : Set Rudvalis.Model) = C ∧ Nat.card C = 64 * 12096 ∧
      ∀ z : E, z ≠ 1 →
        Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) = 12288 := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := ((Y.subgroupOf H).subgroupOf K).map f
  let U := (W.subgroupOf H).subgroupOf K
  let E := U.map f
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  let C := C0.map f
  change normalizer (E : Set Rudvalis.Model) = C ∧ Nat.card C = 64 * 12096 ∧
    ∀ z : E, z ≠ 1 →
      Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) = 12288
  obtain ⟨hNC,_,_⟩ := unitary_original_pushingUp_rudvalis_normalizer
    s hcover hJH hc K hK e c hVW
  change normalizer (B : Set Rudvalis.Model) = C at hNC
  have hEN := (unitary_original_pushingUp_rudvalis_radical_normalizer
    s hcover hJH hc K hK e c hVW).2.2
  change normalizer (E : Set Rudvalis.Model) = C at hEN
  have hlt := unitary_original_pushingUp_rudvalis_module_normalizer_growth
    s hcover hJH hc K hK e c hVW
  change B < normalizer (E : Set Rudvalis.Model) at hlt
  rw [hEN] at hlt
  have hB := (unitary_original_pushingUp_rudvalis_module_and_points
    s hcover hJH hc K hK e c hVW).2.1
  change Nat.card B = 64 * 6048 at hB
  have hsizes := unitary_original_pushingUp_rudvalis_normalizer_sizes
    s hcover hJH hc K hK e c hVW
  dsimp only at hsizes
  rw [hNC] at hsizes
  obtain ⟨n,hn,hncard,hnpoints⟩ := hsizes
  have hn2 : n = 2 := by
    rcases hn with hn | hn
    · subst n
      exfalso
      apply hlt.ne
      apply eq_of_le_of_card_ge hlt.le
      rw [hB,hncard]
    · exact hn
  subst n
  exact ⟨hEN,by simpa only [Nat.reduceMul] using hncard,
    by simpa only [Nat.reduceMul] using hnpoints⟩


/-- The actual escaping odd-actor pair has the exact Rudvalis normalizer,
without a centerlessness premise and with its original relative Sylow. -/
theorem unitary_original_oddActorResidual_exact_normalizer (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (c : sectionCentralizerIn (normalizer (L : Set G)) L),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          ∃ e : K ⧸ center K ≃* Rudvalis.Model,
            W = V.map (MulAut.conj (c : G)).toMonoidHom ∧
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let B := ((Y.subgroupOf H).subgroupOf K).map f
            let E := ((W.subgroupOf H).subgroupOf K).map f
            let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
            B < normalizer (E : Set Rudvalis.Model) ∧
            (∀ P : Subgroup B, E.subgroupOf B ≤ P →
              elementaryAbelianMaxJ P = E.subgroupOf B) ∧
            (normalizer (E : Set Rudvalis.Model) = C ∧ Nat.card C = 64 * 12096 ∧
              ∀ z : E, z ≠ 1 →
                Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) =
                  12288)) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · apply Or.inr
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact ⟨e,unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_module_normalizer_growth s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_thompson s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hcV⟩

/-- The original component intersection is the full module normalizer
already before passing to the center quotient. The full preimage of the
quotient module is its original radical intersection. -/
theorem unitary_original_pushingUp_rudvalis_normalizer_lift (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let U := (W.subgroupOf H).subgroupOf K
    let P := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
    let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
    normalizer (U : Set K) = C0 ∧
      (normalizer (U.map f : Set Rudvalis.Model)).comap f = C0 ∧
      (U.map f).comap f = P := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let U := (W.subgroupOf H).subgroupOf K
  let A := (Y.subgroupOf H).subgroupOf K
  let P := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  change normalizer (U : Set K) = C0 ∧
    (normalizer (U.map f : Set Rudvalis.Model)).comap f = C0 ∧ (U.map f).comap f = P
  have hk : f.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨_,hP,hNC⟩ := unitary_original_pushingUp_rudvalis_radical_normalizer
    s hcover hJH hc K hK e c hVW
  change P = U ⊔ center K at hP
  change normalizer (U.map f : Set Rudvalis.Model) = C0.map f at hNC
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique_at s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,_,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  have hYN := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn
  have hspan : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) = Y := hc.normalized_span_eq hYN
  have hYH : Y ≤ H := hc.component_le.trans hc.local_le
  have hYK := hc.ordinary_component_contains_original K hK
  have hWY : W ≤ Y := hc.module_le.trans hspan.le
  have hWH := hWY.trans hYH
  have hWK := (subgroupOf_mono H hWY).trans hYK
  have hm : U = ⁅U,A⁆ := by
    apply map_injective K.subtype_injective
    apply map_injective H.subtype_injective
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hWK,
      map_subgroupOf_eq_of_le hYK,map_subgroupOf_eq_of_le hWH,
      map_subgroupOf_eq_of_le hYH]
    exact hc.module_commutator.trans (congrArg (fun X => ⁅W,X⁆) hspan)
  have hCA : C0 ≤ normalizer (A : Set K) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hYN hx) (y : G)
  have hCU : C0 ≤ normalizer (U : Set K) :=
    normalizes_moved_of_central_image f U A C0 hk.le hm hCA hNC.symm.le
  have hUC : normalizer (U : Set K) ≤ C0 := by
    rw [←subgroupOf_normalizer_eq hWK,←subgroupOf_normalizer_eq hWH]
    intro x hx
    exact hc.module_normalizer ⟨x.val.property,hx⟩
  refine ⟨le_antisymm hUC hCU,?_,?_⟩
  · rw [hNC,comap_map_eq_self]
    rw [hk]
    exact (center_le_normalizer (U : Set K)).trans hUC
  · rw [comap_map_eq,hk,←hP]

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
