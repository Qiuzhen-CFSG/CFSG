module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResiduals
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsTransport
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.ChapterC.Section02.NormalCoreSetup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# The source setup for every fixed-coset centralizer

For c in the fixed subgroup, L intersects C_G(c e6) in exactly C_L(e6).
Its literal perfect residual is therefore normal in C_G(c e6) intersect N(L).
The actual A6 two-core quotient makes this residual a local C-component.
Uniqueness controls characteristic normalizers of the common two-core,
and A.4.2(7) constructs C.2.3 in the original centralizer.

Source 1.2.4 then places the residual in a normal ambient C-component.
Even characteristic gives that component F* = O2. Excluding a proper
containing component remains the C.2.7 step, not a conclusion of this file.

Source: Aschbacher--Smith, 3.3.22, printed p.597; A.4.2(7), 1.2.4 and
C.2.3, printed pp.57,505,144. Two-core quotient models remain explicit;
final discharge belongs to qt-d-1235-a7-sylow-ambient-residuals.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

lemma coset_component_intersection {c : G} (hc : c ∈ P.fixed) :
    L ⊓ centralizer ({c * (P.six : G)} : Set G) =
      L ⊓ centralizer ({(P.six : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨hxL, hx⟩
    refine ⟨hxL, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := mem_centralizer_singleton_iff.mp hx
    have hxc := hc.2 x hxL
    apply mul_left_cancel (a := c)
    calc
      c * (x * (P.six : G)) = x * (c * (P.six : G)) := by rw [← mul_assoc, ← hxc, mul_assoc]
      _ = c * ((P.six : G) * x) := by rw [he, mul_assoc]
  · rintro ⟨hxL, hx⟩
    refine ⟨hxL, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := mem_centralizer_singleton_iff.mp hx
    have hxc := hc.2 x hxL
    rw [← mul_assoc, hxc, mul_assoc, he, ← mul_assoc]

lemma six_eq_coset_residual {c : G} (hc : c ∈ P.fixed) :
    P.sixGroup = pointResidual L (c * (P.six : G)) := by
  unfold pointResidual
  rw [P.coset_component_intersection hc]
  rfl

lemma coset_local_normalizes {c : G} (hc : c ∈ P.fixed) :
    centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G) ≤
      normalizer (P.sixGroup : Set G) := by
  rw [P.six_eq_coset_residual hc]
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  apply le_trans ?_ inf_normalizer_le_normalizer_inf
  exact le_inf inf_le_right (inf_le_left.trans (le_normalizer))

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

lemma coset_local_component
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) :
    (P.sixGroup.subgroupOf
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G))).IsCComponent := by
  let B := centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)
  have hKB : P.sixGroup ≤ B := le_inf (P.sixGroup_le_coset_centralizer hc)
    ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))
  let K := P.sixGroup.subgroupOf B
  let : K.Normal := normal_subgroupOf_of_le_normalizer (P.coset_local_normalizes hc)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKB).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKB).symm.surjective
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    ((QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKB) (pCore_map_iso 2 _)).trans e6).symm
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : K.Normal).isSubnormal perfect_twoPerfect

include S in
lemma coset_core_characteristic_control
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).characteristicNormalizerClosure ≤
      normalizer (L : Set G) := by
  apply characteristicNormalizerClosure_le_of_unique_twoLocal (isPGroup_pCoreIn 2 _)
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (S.hypothesis.source_normalizer_maximal_unique structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2

lemma coset_core_le {c : G} (hc : c ∈ P.fixed) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      centralizer ({c * (P.six : G)} : Set G) := by
  have hR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact hR.trans (P.coset_sylow_le hc)

lemma coset_characteristic_control
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {c : G} (hc : c ∈ P.fixed) :
    (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (centralizer ({c * (P.six : G)} : Set G))).characteristicNormalizerClosure ≤
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)).subgroupOf
          (centralizer ({c * (P.six : G)} : Set G)) := by
  have h := characteristicNormalizerClosure_subgroupOf_le (P.coset_core_le hc)
    (coset_core_characteristic_control (S := S) structural)
  intro x hx
  exact ⟨x.property, h hx⟩

include S in
lemma coset_core_ne_bot : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
  intro he
  exact S.chosen.ne_bot (bot_unique (he ▸ S.chosen.le_core))

include S in
lemma coset_core_normalizer_le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
  (normalizer_le_characteristicNormalizerClosure_self _ (coset_core_ne_bot (S := S))).trans
    (coset_core_characteristic_control (S := S) structural)

lemma coset_sylow_normalizes
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (T : Subgroup G) ≤ normalizer (P.sixGroup : Set G) := by
  apply le_trans (le_inf (P.coset_sylow_le (P.fixed.one_mem))
    (S.hypothesis.source_sylow_normalizes structural))
  exact P.coset_local_normalizes P.fixed.one_mem

lemma coset_fitting {c : G} (hc : c ∈ P.fixed) :
    generalizedFitting (centralizer ({c * (P.six : G)} : Set G)) =
      pCore 2 (centralizer ({c * (P.six : G)} : Set G)) := by
  obtain ⟨N,hCN,hN⟩ := Finite.exists_le_maximal (P.coset_isTwoLocal hc)
  exact generalizedFitting_eq_pCore_of_sylow_overgroup T _ N
    (P.coset_sylow_le hc) hCN
    (S.hypothesis.simpleQTKE.evenCharacteristic T N hN
      ((P.coset_sylow_le hc).trans hCN))

lemma coset_pushingUp_setup
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    {c : G} (hc : c ∈ P.fixed) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) := by
  let H := centralizer ({c * (P.six : G)} : Set G)
  let N := H ⊓ normalizer (L : Set G)
  have hTN : (T : Subgroup G) ≤ N := le_inf (P.coset_sylow_le hc)
    (S.hypothesis.source_sylow_normalizes structural)
  have hKN : P.sixGroup ≤ N := le_inf (P.sixGroup_le_coset_centralizer hc)
    ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))
  have hTmap : ((T.subtype (P.coset_sylow_le hc) : Sylow 2 H) : Subgroup H).map
      H.subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le (P.coset_sylow_le hc)
  apply ChapterC.pushingUpSetup_of_normal_core (T.subtype (P.coset_sylow_le hc))
    (S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)) hKN inf_le_left
    (P.coset_local_normalizes hc) perfect_twoPerfect
  · rwa [hTmap]
  · rw [hTmap]
    exact M.core_eq.symm
  · exact coset_core_ne_bot (S := S)
  · exact P.coset_characteristic_control structural hc

lemma six_local_family
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.sixGroup ∈ Chapter1.L G (T : Subgroup G) := by
  have hc := P.fixed.one_mem
  have hJ : P.sixGroup ⊔ (T : Subgroup G) ≤
      centralizer ({(1 : G) * (P.six : G)} : Set G) ⊓ normalizer (L : Set G) :=
    sup_le (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer)))
      (le_inf (P.coset_sylow_le hc) (S.hypothesis.source_sylow_normalizes structural))
  refine ⟨(P.coset_local_component e6 hc).subgroupOf_of_le le_sup_left hJ, ?_, ?_⟩
  · exact ⟨T.subtype le_sup_right, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]⟩
  · rw [M.core_eq]
    exact coset_core_ne_bot (S := S)

lemma coset_containing_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) :
    ∃ K : Subgroup (centralizer ({c * (P.six : G)} : Set G)),
      K.IsCComponent ∧ K.Normal ∧
      P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G)) ≤ K ∧
      generalizedFitting K = pCore 2 K := by
  let H := centralizer ({c * (P.six : G)} : Set G)
  let TH : Sylow 2 H := T.subtype (P.coset_sylow_le hc)
  let B := P.sixGroup.subgroupOf H
  have hB : B ∈ Chapter1.L H (TH : Subgroup H) :=
    (Chapter1.mem_LIn_iff_subgroupOf (P.coset_sylow_le hc)
      (P.sixGroup_le_coset_centralizer hc)).mp
      ⟨P.sixGroup_le_coset_centralizer hc, P.six_local_family structural M e6⟩
  have hTB : (TH : Subgroup H) ≤ normalizer (B : Set H) := by
    rw [← subgroupOf_normalizer_eq (P.sixGroup_le_coset_centralizer hc)]
    exact comap_mono (P.coset_sylow_normalizes structural)
  have hH := S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  obtain ⟨K,⟨hK,hBK,hKN⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ TH hB hTB
  refine ⟨K,hK,hKN,hBK,?_⟩
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply subnormal_core_selfCentralizing ?_ K hK.subnormal
  rw [← P.coset_fitting hc]
  exact centralizer_generalizedFitting_le H

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
