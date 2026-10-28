module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingSylow
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.FullSylow

/-!
# Component extraction from the original residual geometry

For an escaping overgroup I, the actual action of M ∩ I on V identifies
its two-core with that of M. The generalized Fitting preimage in I cannot
lie in M ∩ I, since A.4.4 would force the original residual K into M.
The no-chi result and C.2.6 therefore select an escaping C-component.
The component-orbit theorem makes K normalize it, and C.2.4 makes the
intersection core normalize the same component.

Every occurrence of K, I and the intersection uses the original inclusions.
Only `ResidualInput` is used for the plane geometry; no partner-residual
identity or `PlaneUniquenessPreceding` packet is constructed. The action
and no-chi premises are discharged by the independent original-source
owners before the characteristic-two exclusion is assembled.

Source: Aschbacher--Smith, 15.2.19(2) and the component-selection paragraph
of 15.2.23, printed pp.1113 and 1116, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06 ChapterA.Section04
open Chapter1.RadicalExclusions
open PlaneUniquenessPreceding ComponentCatalogue
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

namespace ResidualInput
variable (r : ResidualInput hsource H B)
include r

/-- The core equality in 15.2.19(2), once the actual S₃ action kills O₂(NI). -/
theorem intersection_core_eq_of_centralizes (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hR : (M ⊓ I).pCoreIn 2 ≤ centralizer (V : Set G)) :
    (M ⊓ I).pCoreIn 2 = M.pCoreIn 2 := by
  let C := (centralizer (V : Set G)).subgroupOf M
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hsource.prepared.normalized.trans (normalizer_le_normalizer_centralizer _))
  have hred := hsource.prepared.reduced T hsource.maximal.1.2
  have hQC : pCore 2 M ≤ C := by
    have hi := le_centralizer_iff.mp hred.le_centralizer_pCore
    intro x hx v hv
    exact congrArg M.subtype (hi hx ⟨v,hsource.prepared.le_selected hv⟩ hv)
  have hCC : C.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype,inf_eq_right.mpr hQC]
  have hCI : C.map M.subtype ≤ M ⊓ I := by
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans (r.module_centralizer_le_escape hI))
  have hRC : (M ⊓ I).pCoreIn 2 ≤ C.map M.subtype := by
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf hR ((pCoreIn_le 2 _).trans inf_le_left)
  have hCQ : (C.map M.subtype).pCoreIn 2 = M.pCoreIn 2 := by
    rw [←map_pCoreIn_of_injective 2 C M.subtype M.subtype_injective,hCC]
    rfl
  apply le_antisymm
  · have hh := inf_pCoreIn_le_of_le 2 hCI
    rwa [inf_eq_right.mpr hRC,hCQ] at hh
  · have hQNI : M.pCoreIn 2 ≤ M ⊓ I := (map_mono hQC).trans hCI
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) hQNI
      (inf_le_left.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))

/-- The generalized-Fitting preimage cannot lie in NI: A.4.4 would make its
core normal in I and put the original residual K in M. -/
theorem fitting_preimage_not_le_intersection
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2) :
    ¬ (generalizedFitting (I ⧸ pCore 2 I)).comap
      (QuotientGroup.mk' (pCore 2 I)) ≤ (M ⊓ I).subgroupOf I := by
  intro hle
  have hp : twoGeneralizedFittingPreimage I ≤ I ⊓ M := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x.property,(hle hx).1⟩
  have ha : IntersectionAlternative
      (twoCoreQuotientImage I (twoGeneralizedFittingPreimage I)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl,?_,?_⟩
    · exact (inferInstance : ((generalizedFitting (I ⧸ pCore 2 I)).subgroupOf
        (generalizedFitting (I ⧸ pCore 2 I))).Normal).isSubnormal
    · exact (closure_le _).mpr (fun x hx => hx.1.1)
  have he := lemma_A_4_4_1 I M (twoGeneralizedFittingPreimage I)
    (twoCore_le_fittingPreimage I) hp ha
  rw [inf_comm I M,hcore] at he
  have hIM : I ≤ M := by
    rw [←maximalTwoLocal_normalizer_core hsource.maximal.1.1,←he]
    exact I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  exact r.residual_not_le_left (((le_sup_left.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right).trans hIM)

/-- Select an actual escaping C-component through the quotient by O₂(I).
This is the component-selection paragraph of 15.2.23; it does not yet
assert that the radical normalizes this component. -/
theorem escaping_component_of_no_chi
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) :
    ∃ X : Subgroup I, X.IsCComponent ∧ IsQuasisimple (X ⧸ pCore 2 X) ∧
      generalizedFitting X = pCore 2 X ∧ ¬ X ≤ (M ⊓ I).subgroupOf I :=
  exists_characteristicTwo_cComponent_outside _
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
    (fittingCore_le_intersection_of_no_chi (hsource := hsource) hI hfit hcore hno)
    (r.fitting_preimage_not_le_intersection hI hcore)

/-- The original two-residual K fixes every C-component of I. The source
orbit theorem gives index at most two, and two-perfectness kills that action. -/
theorem residual_normalizes_component (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    {X : Subgroup I} (hX : X.IsCComponent) :
    (pResidual 2 H).map H.subtype ≤ normalizer (X.map I.subtype : Set G) := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right
  let A := K.subgroupOf I
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe hKI).symm.toMonoidHom (subgroupOfEquivOfLe hKI).symm.surjective
  have hs := Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  have hAN : A ≤ normalizer (X : Set I) := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hX with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact le_top
    · let N := normalizer (X : Set I)
      let : N.Normal := normal_of_index_eq_two hi
      have hquot : IsPGroup 2 (I ⧸ N) := IsPGroup.of_card (n := 1) (by
        simpa only [←index_eq_card,pow_one] using hi)
      exact (le_pResidual_of_isPPerfect A hpA).trans (sInf_le ⟨inferInstance,hquot⟩)
  intro k hk
  exact X.le_normalizer_map I.subtype
    (mem_map_of_mem I.subtype (hAN (show (⟨k,hKI hk⟩ : I) ∈ A from hk)))

/-- An original escaping C-component normalized by both the original residual
and O₂(M ∩ I), with only the actual core equality and no-chi input. -/
theorem escaping_normalized_component_of_core
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y) :
    ∃ X : Subgroup G, Normalized H M I X := by
  obtain ⟨Y,hY,hq,hf,hout⟩ := r.escaping_component_of_no_chi hI hfit hcore hno
  let X := Y.map I.subtype
  let e : Y ≃* X := Y.equivMapOfInjective I.subtype I.subtype_injective
  have hXC : X ∈ Chapter1.cComponentsIn I := by
    refine ⟨map_subtype_le _,?_⟩
    have he : X.subgroupOf I = Y :=
      comap_map_eq_self_of_injective I.subtype_injective Y
    rwa [he]
  let := hq
  have hqX : IsQuasisimple (X ⧸ pCore 2 X) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hfX : generalizedFitting X = pCore 2 X := by
    rw [←map_generalizedFitting_equiv e,hf,pCore_map_iso]
  have houtX : ¬ X ≤ M ⊓ I := by
    intro hh
    exact hout (fun y hy => hh (mem_map_of_mem I.subtype hy))
  have hn := r.residual_normalizes_component hI hY
  exact ⟨X,component_normalized_of_no_chi (hsource := hsource) hI hfit hcore hno
    ⟨hXC,hqX,hfX,houtX,hn⟩⟩

end ResidualInput
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
