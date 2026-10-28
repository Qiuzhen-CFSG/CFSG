module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowInputs
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSectionSylow
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer
public import Theory.GroupTheory.CComponent.SixCoverTheta
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiZeroCubicGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple

/-!
# The literal weight-six residual and the Frattini--theta endgame

The residual remains C_L(e)^∞, embedded in the ambient point centralizer H.
Relative normality and its A₆ central quotient identify θ(H) with this
residual, including the triple-cover case. Frattini over the actual section
centralizer Y=C_H(K/O₂(K)) reduces H to Y and the controlled normalizer of Q.
The cubic-generation consequence of C.2.5 then puts Y in N(L).

`SixInput` records the remaining source obligations, not the desired
centralizer bound: component rigidity and the original section Sylow
condition from 12.2.12. Characteristic control follows from the original
normalizer uniqueness; even characteristic supplies the section centralizer
Fitting equality. Constructing it remains the component-enlargement
argument. The local quotient is the same A₆ marking used by `Points.Models` in
source 3.3.22; its construction here cannot use the contrary Sylow-normalizer
hypothesis permitted in that separate application.
The ambient component rigidity and common-core identity remain obligations
of qt-d-1236-1238-point-centralizers before the final local-analysis assembly.
Source: Aschbacher--Smith, 12.3.6, printed p.809; A.3.18 and C.2.5.
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

/-- The original ambient point centralizer. -/
abbrev H (v : V) : Subgroup G := centralizer ({(v : G)} : Set G)
/-- The literal section centralizer, retaining O₂ of the original residual. -/
abbrev Y (v : V) : Subgroup G := twoSectionCentralizer
  (SylowNormalizer.pointResidual L v) (H v)
/-- The two-core used in 12.2.12, embedded in G. -/
abbrev Q (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (L ⊔ (T : Subgroup G)).pCoreIn 2

/-- The precise remaining inputs before the Frattini--theta argument.
None asserts containment of the ambient point centralizer in N(L). -/
structure SixInput (P : SylowNormalizer.Points E) : Prop where
  normalizes : H P.six ≤ normalizer (P.sixGroup : Set G)
  component : (P.sixGroup.subgroupOf (H P.six)).IsCComponent
  quasisimple : IsQuasisimple (P.sixGroup ⧸ pCore 2 P.sixGroup)
  quotient : Nonempty (CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6))
  section_sylow : ∃ R : Sylow 2 (Y (L := L) P.six),
    (R : Subgroup (Y (L := L) P.six)).map (Y (L := L) P.six).subtype = Q T L


include S in
/-- Source 1.4.1 controls the actual core Q before any point argument. -/
theorem core_characteristic_control
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (Q T L).characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
  apply characteristicNormalizerClosure_le_of_unique_twoLocal (isPGroup_pCoreIn 2 _)
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (S.hypothesis.source_normalizer_maximal_unique structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2

include S in
/-- In particular the actual normalizer of Q is controlled. -/
theorem core_normalizer_le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    normalizer (Q T L : Set G) ≤ normalizer (L : Set G) := by
  have hne : Q T L ≠ ⊥ := fun he => S.chosen.ne_bot
    (le_bot_iff.mp (he ▸ S.chosen.le_core))
  exact (normalizer_le_characteristicNormalizerClosure_self _ hne).trans
    (core_characteristic_control (S := S) structural)

include S in
/-- The original even-characteristic assumption applies to the actual point
centralizer, and hence to its normal section centralizer. -/
theorem section_fitting_of_normalizes (v : V) (hv : v ≠ 1)
    (hcentral : (v : G) ∈ centralizer (T : Set G))
    (hn : H v ≤ normalizer (SylowNormalizer.pointResidual L v : Set G)) :
    generalizedFitting (Y (L := L) v) = pCore 2 (Y (L := L) v) := by
  let C := H v
  let A := Y (L := L) v
  let := S.chosen.elementary
  have ho : orderOf (v : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ v.property) (fun h => hv (Subtype.ext h))
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hcentral t ht)
  obtain ⟨M,hCM,hM⟩ := Finite.exists_le_maximal (isTwoLocal_involution_centralizer ho)
  have hCf : generalizedFitting C = pCore 2 C :=
    generalizedFitting_eq_pCore_of_sylow_overgroup T C M hTC hCM
      (S.hypothesis.simpleQTKE.evenCharacteristic T M hM (hTC.trans hCM))
  have hCc : centralizer (pCore 2 C : Set C) ≤ pCore 2 C := by
    rw [←hCf]
    exact centralizer_generalizedFitting_le C
  have hAC : A ≤ C := ChapterA.Section04.twoSectionCentralizer_le _ _
  have hCA : C ≤ normalizer (A : Set G) :=
    ChapterA.Section04.twoSectionCentralizer_normalized _ _ hn
  let : (A.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCA
  have hc := normal_core_selfCentralizing hCc (A.subgroupOf C)
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hAC)).mp hc)

private def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

/-- Component rigidity identifies theta in the actual point centralizer. -/
theorem six_theta (P : SylowNormalizer.Points E) (B : SixInput P) :
    closure {x : G | x ∈ H P.six ∧ orderOf x = 3} = P.sixGroup := by
  let K := P.sixGroup
  let C := H P.six
  have hKC : K ≤ C := (map_subtype_le _).trans inf_le_right
  let A := K.subgroupOf C
  let : A.Normal := normal_subgroupOf_of_le_normalizer B.normalizes
  let : IsQuasisimple (K ⧸ pCore 2 K) := B.quasisimple
  let eA : (A ⧸ pCore 2 A) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKC) (pCore_map_iso 2 _)
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eA.symm
  obtain ⟨eK⟩ := B.quotient
  have hquot : ((A ⧸ pCore 2 A) ⧸ center (A ⧸ pCore 2 A)) ≃*
      alternatingGroup (Fin 6) :=
    (centerQuotientCongr eA).trans
      ((centralPreimageQuotientEquiv (pCore 2 K)).symm.trans eK)
  have hne : P.six ≠ 1 := by
    intro he
    have hw := P.six_weight
    rw [he,map_one] at hw
    have hz : weight (0 : Word) = 0 := by decide
    exact (by decide : (0 : ℕ) ≠ 6) (hz.symm.trans hw)
  have ho : orderOf (P.six : G) = 2 := by
    let := S.chosen.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ P.six.property)
      (fun h => hne (Subtype.ext h))
  have hc := S.hypothesis.simpleQTKE.involution_centralizer_sqtk ho
  have he := SixCComponentTheta.cubic_closure_eq_of_central_quotient_six A
    B.component hquot (hc.stronglyQuasithin 3 Nat.prime_three (by decide))
  have hm := congrArg (map C.subtype) he
  rw [MonoidHom.map_closure,map_subgroupOf_eq_of_le hKC] at hm
  convert hm using 1
  congr 1
  ext x
  constructor
  · rintro ⟨hx,h3⟩
    exact ⟨⟨x,hx⟩,(C.orderOf_coe ⟨x,hx⟩).symm.trans h3,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,(C.orderOf_coe y).trans hy⟩

/-- Frattini over the literal quotient-action centralizer and the C.2.5
cubic cover finish 12.3.6, conditional on the component analysis above. -/
theorem six_centralizer_le (P : SylowNormalizer.Points E) (B : SixInput P)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) : H P.six ≤ normalizer (L : Set G) := by
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
        (core_characteristic_control (S := S) structural)
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
  apply core_normalizer_le (S := S) structural
  have hn := ((R' : Subgroup A').map A'.subtype).le_normalizer_map C.subtype
    (mem_map_of_mem C.subtype hc)
  rwa [hmap] at hn

/-- Application of the literal section-Sylow calculation: only component
rigidity, its actual central quotient and the common two-core remain. -/
theorem six_centralizer_le_of_component_core (P : SylowNormalizer.Points E)
    (hn : H P.six ≤ normalizer (P.sixGroup : Set G))
    (hc : (P.sixGroup.subgroupOf (H P.six)).IsCComponent)
    (hq : IsQuasisimple (P.sixGroup ⧸ pCore 2 P.sixGroup))
    (he : Nonempty (CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6)))
    (hcore : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 = Q T L)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    H P.six ≤ normalizer (L : Set G) :=
  six_centralizer_le P
    ⟨hn,hc,hq,he,P.six_section_sylow_of_core_eq hcore⟩ structural

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
