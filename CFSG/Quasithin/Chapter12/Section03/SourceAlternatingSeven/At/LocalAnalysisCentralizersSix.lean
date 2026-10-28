module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSix
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction

/-!
# LocalAnalysisCentralizersSix at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersSix`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode ChapterA.Section04

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace PointCentralizers

include S in

theorem core_characteristic_control_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (Q T L).characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
  apply characteristicNormalizerClosure_le_of_unique_twoLocal (isPGroup_pCoreIn 2 _)
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (S.hypothesis.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2

include S in

theorem core_normalizer_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    normalizer (Q T L : Set G) ≤ normalizer (L : Set G) := by
  have hne : Q T L ≠ ⊥ := fun he => S.chosen.ne_bot
    (le_bot_iff.mp (he ▸ S.chosen.le_core))
  exact (normalizer_le_characteristicNormalizerClosure_self _ hne).trans
    (core_characteristic_control_at (S := S) structural)

private def centerQuotientCongr_at {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

theorem six_centralizer_le_at (P : SylowNormalizer.Points E) (B : SixInput P)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) : H P.six ≤ normalizer (L : Set G) := by
  let C := H P.six
  let A := Y (L := L) P.six
  let M := normalizer (L : Set G)
  have hAC : A ≤ C := twoSectionCentralizer_le _ _
  have hCA : C ≤ normalizer (A : Set G) :=
    twoSectionCentralizer_normalized _ _ B.normalizes
  obtain ⟨R,hR⟩ := B.section_sylow
  have hAM : A ≤ M := by
    have hRA : Q T L ≤ A := hR ▸ map_subtype_le _
    have hR' : (R : Subgroup A) = (Q T L).subgroupOf A := by
      apply map_injective A.subtype_injective
      rw [hR,map_subgroupOf_eq_of_le hRA]
    have hne : P.six ≠ 1 := by
      intro he
      have hw := P.six_weight
      rw [he,map_one] at hw
      exact (by decide : (0 : ℕ) ≠ 6) hw
    have ho : orderOf (P.six : G) = 2 := by
      let := S.chosen.elementary
      exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ P.six.property)
        (fun h => hne (Subtype.ext h))
    have hC := S.hypothesis.simpleQTKE.involution_centralizer_sqtk ho
    have hA : IsSQTK KnownSimple.IsKnownSimple A := by
      let i := inclusion hAC
      exact ⟨hC.stronglyQuasithin.of_injective i (inclusion_injective hAC),
        hC.isKGroup.of_injective i (inclusion_injective hAC)⟩
    have hcontrol : (R : Subgroup A).characteristicNormalizerClosure ≤ M.subgroupOf A := by
      rw [hR']
      exact characteristicNormalizerClosure_subgroupOf_le hRA
        (core_characteristic_control_at (S := S) structural)
    obtain ⟨r,_,blocks,hblocks,_,_,hcover⟩ :=
      ChapterC.RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple
        hA (section_fitting_of_normalizes (S := S) P.six hne P.six_central B.normalizes)
        R (M.subgroupOf A) hcontrol
    intro a ha
    obtain ⟨m,b,hprod⟩ := hcover ⟨a,ha⟩
    have hb (i : Fin r) : ((b i : A) : G) ∈ M := by
      have hc := (hblocks i).2.le_cubic_closure (H := (⊤ : Subgroup A)) le_top
      have hθ : closure {x : A | x ∈ (⊤ : Subgroup A) ∧ orderOf x = 3} ≤ M.subgroupOf A := by
        apply (closure_le _).mpr
        intro x hx
        have hm : (x : G) ∈ closure {x : G | x ∈ C ∧ orderOf x = 3} :=
          subset_closure ⟨hAC x.property,(A.orderOf_coe x).trans hx.2⟩
        rw [six_theta P B] at hm
        exact L.le_normalizer ((map_subtype_le _ hm).1)
      exact hθ (hc (b i).property)
    have hm := (M.subgroupOf A).mul_mem m.property
      ((M.subgroupOf A).list_prod_mem (by
        intro x hx
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact hb i))
    rw [←hprod] at hm
    exact hm
  let A' := A.subgroupOf C
  let : A'.Normal := normal_subgroupOf_of_le_normalizer hCA
  let e : A ≃* A' := (subgroupOfEquivOfLe hAC).symm
  let R' : Sylow 2 A' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((R' : Subgroup A').map A'.subtype).map C.subtype = Q T L := by
    change (((R : Subgroup A).map e.toMonoidHom).map A'.subtype).map C.subtype = _
    rw [map_map,map_map]
    exact hR
  have hfr : normalizer ((R' : Subgroup A').map A'.subtype : Set C) ⊔ A' = ⊤ :=
    R'.normalizer_sup_eq_top
  have hm := congrArg (map C.subtype) hfr
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hAC] at hm
  change C ≤ M
  rw [←hm]
  apply sup_le ?_ hAM
  rintro _ ⟨c,hc,rfl⟩
  apply core_normalizer_le_at (S := S) structural
  have hn := ((R' : Subgroup A').map A'.subtype).le_normalizer_map C.subtype
    (mem_map_of_mem C.subtype hc)
  rwa [hmap] at hn

theorem six_centralizer_le_of_component_core_at (P : SylowNormalizer.Points E)
    (hn : H P.six ≤ normalizer (P.sixGroup : Set G))
    (hc : (P.sixGroup.subgroupOf (H P.six)).IsCComponent)
    (hq : IsQuasisimple (P.sixGroup ⧸ pCore 2 P.sixGroup))
    (he : Nonempty (CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6)))
    (hcore : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 = Q T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    H P.six ≤ normalizer (L : Set G) :=
  six_centralizer_le_at P
    ⟨hn,hc,hq,he,P.six_section_sylow_of_core_eq hcore⟩ structural

end PointCentralizers

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

