module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalResidual
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Point
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.RankOne
public import Theory.SpecificGroups.PSL3.BinaryComparison

/-!
# The original exchanged linear-three component

The actual PSL₃(2) model is transported through PSL₂(7). The odd rank bound
from the original flag-involution centralizer and the index-two component
normalizer identify O^{3′}(H) with the T-orbit of K. The natural local flag
then supplies every remaining input to the marked wreath construction:
two-perfectness, the cubic quotient, theta, solvable exclusion and the
covered factorization. Its D₈ automizer contradicts the original E₄ image.

The final application restricts to ⟨K^T⟩L₁T, retaining the actual relative
component and transporting both star models through K/O₂(K). Thus every
original PSL₃(2) component is normal in H and KL₁T belongs to Hz.

The genuine earlier 12.2.1, F.9, 13.5.4 and 13.3.9 hypotheses remain
explicit. The Suzuki branch and final 13.8.16--17 assembly remain with
qt-d-138-components-source; original setup discharge remains with
qt-d-1381-source.
Source: Aschbacher--Smith, 1.2.2(a), printed p.504, and 13.8.16(1), p.952.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The exceptional comparison supplies the odd-prime model without unfolding matrices
inside the original component proof. -/
private theorem binary_three_model : ClassicalGroup.IsPSL Matrix.PSL3Two.PSL 2 7 :=
  ⟨ZMod 7, inferInstance, inferInstance, Nat.card_zmod 7,
    ⟨Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩⟩

private theorem binary_three_card : 3 ∣ Nat.card Matrix.PSL3Two.PSL := by
  rw [← Nat.card_congr Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.toEquiv,
    Atlas.Comparisons.Exceptional.psl2Seven_card]
  decide

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)

include d h hF9all hcentral hcomm hsource hH hKH hK hmoving in
/-- The prime-to-three residual is the literal moving component orbit. -/
theorem threeResidual
    (eK : Source.starImage H K ≃* Matrix.PSL3Two.PSL) :
    (primeToResidual 3 H).map H.subtype = conjugateSpanBy K (T : Subgroup G) := by
  have hi := LinearTwo.Original.moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  let e : ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) ≃* Source.starImage H K :=
    cComponentTwoCoreQuotientEquiv hK
  let := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    (e.trans eK).isSimpleGroup
  have hd : 3 ∣ Nat.card ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) := by
    rw [Nat.card_congr (e.trans eK).toEquiv]
    exact binary_three_card
  obtain ⟨z, hz, _, _, _, hG⟩ := LocalFitting.line_involution d
  have hr : primeRank 3 H ≤ 2 :=
    ((d.counterexample.qtke.toIsQTKE.involution_centralizer_stronglyQuasithin hz).of_injective
      (inclusion (hH.2.1.trans hG)) (inclusion_injective (hH.2.1.trans hG)))
        3 Nat.prime_three (by decide)
  have hm : ClassicalGroup.IsPSL ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) 2 7 :=
    binary_three_model.of_mulEquiv (e.trans eK)
  have he := Chapter1.Section02.nonnormal_component_threeResidual hK hi hd hr
    (.linear_prime 7 (by decide) (by decide) hm)
  have he' := congrArg (map H.subtype) he
  rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hKH, ← MonoidHom.range_eq_map, range_subtype] at he'
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨t, ht, htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  rw [he', orbit_eq_two_conjugates H K H hKH le_rfl hi (hTH ht) htn,
    orbit_eq_two_conjugates H K T hKH hTH hi ht htn]

include d h hF9all hcentral hcomm hsource hH hKH hK hmoving in
/-- Construct the marked moving pair without a residual or local-model premise. -/
theorem sourcePair
    (eK : Source.starImage H K ≃* Matrix.PSL3Two.PSL)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H) :
    Nonempty (WreathOvergroup.SourcePair.Input H (one L T V₁) T K
      (conjugateSpanBy K (T : Subgroup G))) := by
  obtain ⟨t, ht, htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  have hi := LinearTwo.Original.moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  exact ⟨{
    ambientSylow := T
    ambientSylow_eq := rfl
    base_le := hH.1.2
    component_le := hKH
    component := hK
    quasisimple := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
    model := eK
    mover := t
    mover_mem := ht
    mover_not_normalizes := htn
    orbit_index := hi
    orbit_eq := orbit_eq_two_conjugates H K T hKH (le_sup_right.trans hH.1.2) hi ht htn
    generated := by simpa only [sup_assoc] using hgen.symm
    residual := threeResidual d h hF9all hcentral hcomm hsource hH hKH hK hmoving eK
    seed_twoPerfect := residual_isPPerfect _
    seed_quotient_card := Section07.ModelExclusions.point_residual_quotient_card (localNaturalSetup d)
    seed_normalized := T_normalizes_one L T V₁ d.line_stable
    solvable_base := LocalFitting.local_solvable d }⟩

include d h hF9all hcentral hcomm hsource hH hKH hK in
/-- Exclude the exchanged PSL₃(2) component in the original generated overgroup. -/
theorem false_of_source
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 3 2)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let eK : Source.starImage H K ≃* Matrix.PSL3Two.PSL :=
    (e.trans (Matrix.PSL3.binaryEquivPsl2Seven F hF)).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
  obtain ⟨s⟩ := sourcePair d h hF9all hcentral hcomm hsource hH hKH hK hmoving eK hgen
  have hMN : M = normalizer (L : Set G) := d.local_normalizer
  apply exclude_l3_branch L V V₁ H G₁ K (conjugateSpanBy K (T : Subgroup G)) T
    (le_sup_left.trans d.normalizes_V) (local_point_models d) d.normalizes_L d.line_stable
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) d.line_card
    ?_ ?_ s hH.2.1 ?_ ?_
  · intro c
    rcases local_quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
    · have hh := Nat.card_congr (centerCongr (c.quotientEquiv.symm.trans e)).toEquiv
      rw [Representation.Hexacode.even_center_card,
        alternatingGroup.center_eq_bot (by simp), card_bot] at hh
      omega
    · obtain ⟨a⟩ := local_covered_flag_model d e he
      exact CoverFactorization.source_factorization a
  · intro J _ hJG _
    obtain ⟨z, hz, _, _, _, hG⟩ := LocalFitting.line_involution d
    exact ((d.counterexample.qtke.toIsQTKE.involution_centralizer_stronglyQuasithin hz).of_injective
      (inclusion (hJG.trans hG)) (inclusion_injective (hJG.trans hG)))
        3 Nat.prime_three (by decide)
  · intro J hJ hJG hs
    rw [← hMN]
    exact SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource J hJ hJG hs
  · rw [← hMN]
    exact (Section07.ModelExclusions.theta_intersection (localNaturalSetup d) h hH).symm


include d h hF9all hcentral hcomm hsource hH hKH hK in
/-- The linear-three case of 13.8.16(1) on an arbitrary original overgroup. -/
theorem source_normal_and_overgroup
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 3 2) :
    (K.subgroupOf H).Normal ∧
      K ⊔ (one L T V₁ ⊔ (T : Subgroup G)) ∈ Source.Hz (one L T V₁) T G₁ M := by
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
  have hKJ : K ≤ J := (le_conjugateSpanBy K (T : Subgroup G)).trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hLJ : one L T V₁ ≤ J := le_sup_left.trans le_sup_right
  have hJH : J ≤ H := sup_le
    (conjugateSpanBy_le hKH ((le_sup_right.trans hH.1.2).trans H.le_normalizer)) hH.1.2
  have hK' : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hJ : J ∈ Source.Hz (one L T V₁) T G₁ M := by
    have hm := (LocalFitting.source_component d hH hsource
      (SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource)
      K hKH hK).2.1
    have he : (K ⊔ (T : Subgroup G)) ⊔ one L T V₁ = J := by
      apply le_antisymm (sup_le (sup_le hKJ hTJ) hLJ)
      apply sup_le
      · exact conjugateSpanBy_le (le_sup_left.trans le_sup_left)
          ((le_sup_right.trans le_sup_left).trans ((K ⊔ (T : Subgroup G)) ⊔ one L T V₁).le_normalizer)
      · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
    exact he ▸ hm
  have hspan : conjugateSpanBy K (T : Subgroup G) = K := by
    by_contra hmoving
    let e := (componentStarEquiv J K hKJ hK').symm.trans (componentStarEquiv H K hKH hK)
    exact false_of_source d h hF9all hcentral hcomm hsource hJ hKJ hK'
      (hmodel.of_mulEquiv e) rfl hmoving
  refine ⟨normal_of_sylow_span_eq H K T hKH (le_sup_right.trans hH.1.2)
    (SolvableSource.source_component_orbit d hF9all
      (SolvableSource.covered_normalizer_source d h) hcentral hcomm hsource hH K hK)
    hspan, ?_⟩
  change conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) ∈ _ at hJ
  rwa [hspan] at hJ

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.Original
