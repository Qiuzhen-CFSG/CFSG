module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Fitting
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Sylow
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CharacteristicTwo

/-!
# Escaping components in the original plane centralizer

The cubic in the pointwise plane action kills the image of O₂(C_M(A)).
Consequently this core is O₂(C_G(V)). The latter contains V and is normalized
by LT, so source uniqueness puts its full normalizer in M=N_G(L).
A.4.4 therefore forces O₂,F*(C_G(A)) to escape M whenever C_G(A) does.
Together with the proved Fitting-preimage containment, this constructs an
actual relative quasisimple C-component outside M, with F*=O₂.

C.2.4 gives either a full Sylow intersection with Q or normalization by Q.
In the normalized branch the existing Sylow repositioning constructs the
literal LocalData. The moved-component branch is retained explicitly: its
second-cubic rank contradiction, C.2.7 inspection and the chief-factor
endpoint remain with the original plane-centralizer assembly owner.

This route does not need the stronger intermediate identity Q=O₂(C_M(A)).
All cores, normal closures and quotient maps retain their relative ambient
groups. Source: Aschbacher--Smith 13.3.12, printed p.889, A.4.4 and C.2.4.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The cubic action identifies the core of the literal local plane centralizer. -/
theorem Context.plane_core_eq_centralizer_core (s : Context T L V) (d : MarkedPlane V) :
    (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).pCoreIn 2 =
      (centralizer (V : Set G)).pCoreIn 2 := by
  let M := centralizer (d.A : Set G) ⊓ normalizer (L : Set G)
  let C := centralizer (V : Set G)
  have hCM : C ≤ M := le_inf (Subgroup.centralizer_le d.le_module)
    s.earlier_geometry.1.centralizer_le
  have hMC : M ≤ normalizer (C : Set G) :=
    (s.plane_local_control d).2.2.2.trans (normalizer_le_normalizer_centralizer V)
  let f := s.planeCentralizerAction d
  obtain ⟨e⟩ := pointwise_plane_equiv_s3
  let f3 := e.toMonoidHom.comp f
  obtain ⟨n, hn, hnH, hnL, _⟩ := s.marked_cubic d.chart d.coordinates
    d.equivariant d.A d.le_module d.plane_space
  let x : M := ⟨n.val, hnH, L.le_normalizer hnL⟩
  have hx : orderOf (f3 x) = 3 := by
    rw [show f3 x = e (f x) from rfl, e.orderOf_eq]
    rw [← Subgroup.orderOf_coe (f x)]
    rw [show (f x).val = d.chart (V.normalizerMonoidHom.rangeRestrict n) from
      s.planeCentralizerAction_apply d x]
    rw [hn, orderOf_cubic]
  have hpC : M.pCoreIn 2 ≤ C := by
    rintro y ⟨z, hz, rfl⟩
    have hz3 := twoCore_le_ker_of_permThree_cubic f3 x hx hz
    have hz1 : f z = 1 := e.injective (by exact hz3.trans (map_one e).symm)
    have hzker : z ∈ (s.planeCentralizerAction d).ker := hz1
    rw [s.planeCentralizerAction_ker d] at hzker
    exact hzker
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) hpC
      (hCM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  · exact pCoreIn_mono_of_normalizes hCM hMC

/-- Source uniqueness controls the full normalizer of the nontrivial kernel core. -/
theorem Context.centralizer_core_normalizer_le (s : Context T L V) :
    normalizer ((centralizer (V : Set G)).pCoreIn 2 : Set G) ≤
      normalizer (L : Set G) := by
  let C := centralizer (V : Set G)
  have hVP : V ≤ C.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 V) V.le_centralizer
    (Subgroup.centralizer_le_normalizer _)
  have hn : L ⊔ (T : Subgroup G) ≤ normalizer (C.pCoreIn 2 : Set G) :=
    ((sup_le s.chosen.normalizes s.earlier_geometry.1.sylow_le_normalizer).trans
      (normalizer_le_normalizer_centralizer V)).trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hu := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  exact normalizer_le_of_unique_maximalTwoLocal hu.2 (isPGroup_pCoreIn 2 C)
    (fun hb => s.chosen.ne_bot (le_bot_iff.mp (hb ▸ hVP))) hn

/-- A.4.4 forces the generalized-Fitting preimage to escape with its centralizer. -/
theorem Context.plane_generalizedFitting_escape (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ¬ ChapterA.Section04.twoGeneralizedFittingPreimage (centralizer (d.A : Set G)) ≤
      centralizer (d.A : Set G) ⊓ normalizer (L : Set G) := by
  let H := centralizer (d.A : Set G)
  intro hpre
  have halt : ChapterA.Section04.IntersectionAlternative
      (ChapterA.Section04.twoCoreQuotientImage H
        (ChapterA.Section04.twoGeneralizedFittingPreimage H)) := by
    rw [ChapterA.Section04.twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl, ?_, ?_⟩
    · exact (inferInstance : ((generalizedFitting (H ⧸ pCore 2 H)).subgroupOf
        (generalizedFitting (H ⧸ pCore 2 H))).Normal).isSubnormal
    · exact (closure_le _).mpr (fun x hx => hx.1.1)
  have hrecover := ChapterA.Section04.lemma_A_4_4_1 H (normalizer (L : Set G))
    (ChapterA.Section04.twoGeneralizedFittingPreimage H)
    (ChapterA.Section04.twoCore_le_fittingPreimage H) hpre halt
  have he : H.pCoreIn 2 = (centralizer (V : Set G)).pCoreIn 2 :=
    hrecover.trans (s.plane_core_eq_centralizer_core d)
  apply hout
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  rw [he] at hn
  exact hn.trans s.centralizer_core_normalizer_le

/-- An actual escaping relative component; no normalization is assumed. -/
theorem Context.exists_outside_component (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G,
      J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)) ∧
      IsQuasisimple (J ⧸ pCore 2 J) ∧ generalizedFitting J = pCore 2 J ∧
      ¬ J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G) := by
  let H := centralizer (d.A : Set G)
  let M := H ⊓ normalizer (L : Set G)
  have hf : twoFittingCore H ≤ M.subgroupOf H :=
    map_le_iff_le_comap.mp (s.plane_twoFittingCore_le d)
  have hg : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
    intro h
    exact s.plane_generalizedFitting_escape d hout (map_le_iff_le_comap.mpr h)
  obtain ⟨J,hJ,hq,hfJ,houtJ⟩ := exists_characteristicTwo_cComponent_outside
    (M.subgroupOf H) (s.centralizer_characteristicTwo d.A d.le_module d.ne_bot) hf hg
  let Jg := J.map H.subtype
  let e : J ≃* Jg := equivMapOfInjective J H.subtype H.subtype_injective
  refine ⟨Jg, ?_, ?_, ?_, ?_⟩
  · refine ⟨map_subtype_le _, ?_⟩
    change (Jg.comap H.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact hJ
  · exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  · rw [← map_generalizedFitting_equiv e, hfJ, pCore_map_iso]
  · intro h
    exact houtJ (map_le_iff_le_comap.mp h)

/-- Retain the normal closure inside C_M(A), now regarded inside C_G(A). -/
theorem Context.plane_internal_closure_sylow (s : Context T L V) (d : MarkedPlane V) :
    ChapterC.IsSylowInNormalClosure
      (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (centralizer (d.A : Set G)))
      ((centralizer (d.A : Set G) ⊓ normalizer (L : Set G)).subgroupOf
        (centralizer (d.A : Set G))) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let H := centralizer (d.A : Set G)
  let M := H ⊓ normalizer (L : Set G)
  let C := centralizer (V : Set G)
  let MH := M.subgroupOf H
  let R := Q.subgroupOf H
  let N := normalClosure (R.subgroupOf MH : Set MH)
  have hQH : Q ≤ H := (s.plane_local_control d).1
  have hQM : Q ≤ M := le_inf hQH
    ((pCoreIn_le 2 _).trans (sup_le L.le_normalizer s.chosen.sylow_normalizes_component))
  have hCH : C ≤ H := Subgroup.centralizer_le d.le_module
  have hn : MH ≤ normalizer (C.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hCH]
    intro x hx
    exact ((s.plane_local_control d).2.2.2.trans
      (normalizer_le_normalizer_centralizer V)) hx
  let : ((C.subgroupOf H).subgroupOf MH).Normal :=
    normal_subgroupOf_of_le_normalizer hn
  have hNC : N ≤ (C.subgroupOf H).subgroupOf MH :=
    normalClosure_le_normal (fun x hx => s.chosen.core_centralizes hx)
  have hRN : R.subgroupOf MH ≤ N := subset_normalClosure
  have hp : IsPGroup 2 ((R.subgroupOf MH).subgroupOf N) :=
    (isPGroup_pCoreIn 2 _).comap_subtype.comap_subtype.comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  let f : N →* G := H.subtype.comp (MH.subtype.comp N.subtype)
  let D := (P : Subgroup N).map f
  have hQD : Q ≤ D := by
    intro q hq
    exact ⟨⟨⟨⟨q,hQH hq⟩,hQM hq⟩,hRN hq⟩,hP hq,rfl⟩
  have hDC : D ≤ C := by
    rintro x ⟨y,hy,rfl⟩
    exact hNC y.property
  have he : D = Q :=
    (Chapter1.isSylowIn_iff.mp (show Chapter1.IsSylowIn 2 Q C from
      s.core_sylow_centralizer)).2.2 D (P.isPGroup'.map f) hQD hDC
  refine ⟨P, ?_⟩
  apply map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le hQH, map_map, map_map]
  exact he

/-- The source extraction, with both genuine C.2.4 alternatives retained. -/
theorem Context.outside_component_sylow_or_normalized
    (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J : Subgroup G,
      J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)) ∧
      IsQuasisimple (J ⧸ pCore 2 J) ∧ generalizedFitting J = pCore 2 J ∧
      ¬ J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G) ∧
      ((∃ S : Sylow 2 J, (S : Subgroup J).map J.subtype =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ J) ∨
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (J : Set G)) := by
  obtain ⟨J,hJ,hq,hf,ho⟩ := s.exists_outside_component d hout
  let := hq
  refine ⟨J,hJ,hq,hf,ho,?_⟩
  exact ChapterC.Section02Source.sylow_intersection_or_normalizes_in_of_characteristicTwo
    (centralizer (d.A : Set G)) ((L ⊔ (T : Subgroup G)).pCoreIn 2)
    (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) J
    (s.plane_local_control d).2.1 (s.plane_local_control d).1 hJ.1
    (s.core_plane_radical d) (s.plane_local_control d).2.2.1
    (s.plane_internal_closure_sylow d) hJ.2
    (s.centralizer_characteristicTwo d.A d.le_module d.ne_bot)

/-- Only a genuinely moved component can obstruct the existing LocalData assembly. -/
theorem Context.localData_or_moved_component (s : Context T L V) (d : MarkedPlane V)
    (hout : ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G)) :
    (∃ J : Subgroup G, Nonempty (LocalData T L d J)) ∨
      ∃ J : Subgroup G,
        J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)) ∧
        IsQuasisimple (J ⧸ pCore 2 J) ∧ generalizedFitting J = pCore 2 J ∧
        ¬ J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G) ∧
        ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (J : Set G) ∧
        ∃ S : Sylow 2 J, (S : Subgroup J).map J.subtype =
          (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ J := by
  obtain ⟨J,hJ,hq,hf,ho,ha⟩ := s.outside_component_sylow_or_normalized d hout
  by_cases hn : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (J : Set G)
  · exact Or.inl ⟨J,s.localData_of_normalized_component d J hJ hq hf ho hn⟩
  · exact Or.inr ⟨J,hJ,hq,hf,ho,hn,ha.resolve_right hn⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
