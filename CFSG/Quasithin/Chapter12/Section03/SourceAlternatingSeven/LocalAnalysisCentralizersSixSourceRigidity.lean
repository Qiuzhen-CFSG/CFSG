module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSixSource
public import Theory.Alternating.SixSolvableSection
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.CentralSixStarModels


/-!
# Ambient weight-six centralizers and the Thompson consequences

The six-point residual is a component of its literal local intersection.
The genuine containment theorem and the C.2.7 star exclusions show that
it cannot enlarge in any fixed-coset centralizer. The proof retains both
the alternating-six and triple-cover two-core quotients. Relative normality
then supplies the original section Sylow, and the Frattini--theta argument
controls the ambient point centralizer.

This proves 12.3.6 and discharges the weight-six premise of every clause
of 12.3.7. The final LocalAnalysis application retains only the weight-two
component and moved-module obligations, owned by this task before the
qt-d-1231-local-analysis assembly. Source: Aschbacher--Smith, printed
pp.809--810.
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

noncomputable def sixRadicalEquiv :
    (P.sixGroup ⧸ solvableRadical P.sixGroup) ≃* alternatingGroup (Fin 6) := by
  let : IsQuasisimple (P.sixGroup ⧸ pCore 2 P.sixGroup) :=
    E.sixResidualCore_quasisimple P.six P.six_weight
  exact (QuotientGroup.quotientMulEquivOfEq
    Theory.Alternating.SixSolvableSection.radical_eq_centralPreimage).trans
      (E.sixResidualCentralEquiv P.six P.six_weight)

lemma coset_local_component_central
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
  let : IsQuasisimple (P.sixGroup ⧸ pCore 2 P.sixGroup) :=
    E.sixResidualCore_quasisimple P.six P.six_weight
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKB) (pCore_map_iso 2 _)).symm
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2)
    (inferInstance : K.Normal).isSubnormal (by
      intro N hN hp
      let := hN
      let := hp.isNilpotent
      exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N))

lemma six_local_family_central
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models) :
    P.sixGroup ∈ Chapter1.L G (T : Subgroup G) := by
  have hc := P.fixed.one_mem
  have hJ : P.sixGroup ⊔ (T : Subgroup G) ≤
      centralizer ({(1 : G) * (P.six : G)} : Set G) ⊓ normalizer (L : Set G) :=
    sup_le (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer)))
      (le_inf (P.coset_sylow_le hc) (S.hypothesis.source_sylow_normalizes structural))
  refine ⟨(P.coset_local_component_central hc).subgroupOf_of_le le_sup_left hJ, ?_, ?_⟩
  · exact ⟨T.subtype le_sup_right, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]⟩
  · rw [M.core_eq]
    exact coset_core_ne_bot (S := S)

lemma coset_containing_component_central
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
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
      ⟨P.sixGroup_le_coset_centralizer hc, P.six_local_family_central structural M⟩
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

lemma coset_containing_component_quasisimple_central
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    {c : G} (hc : c ∈ P.fixed) :
    ∃ K : Subgroup (centralizer ({c * (P.six : G)} : Set G)),
      K.IsCComponent ∧ K.Normal ∧
      P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G)) ≤ K ∧
      generalizedFitting K = pCore 2 K ∧ IsQuasisimple (K ⧸ pCore 2 K) := by
  obtain ⟨K,hK,hn,hBK,hf⟩ := P.coset_containing_component_central structural M hc
  refine ⟨K,hK,hn,hBK,hf,?_⟩
  apply ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank
    (S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)) hK
  have hr := Theory.Alternating.SixSolvableSection.rank_ge_two P.sixRadicalEquiv
  have he := primeRank_equiv 3 (subgroupOfEquivOfLe (P.sixGroup_le_coset_centralizer hc))
  exact (he ▸ hr).trans
    (_root_.primeRank_le_of_injective 3 (inclusion hBK) (inclusion_injective hBK))

lemma coset_container_eq_of_le_local_central
    {c : G} (hc : c ∈ P.fixed)
    {K : Subgroup (centralizer ({c * (P.six : G)} : Set G))}
    (hK : K.IsCComponent)
    (hBK : P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G)) ≤ K)
    (hKM : K.map (centralizer ({c * (P.six : G)} : Set G)).subtype ≤ normalizer (L : Set G)) :
    K.map (centralizer ({c * (P.six : G)} : Set G)).subtype = P.sixGroup := by
  let H := centralizer ({c * (P.six : G)} : Set G)
  let N := H ⊓ normalizer (L : Set G)
  have hKH : (K.map H.subtype).subgroupOf H = K :=
    comap_map_eq_self_of_injective H.subtype_injective K
  have hKN : K.map H.subtype ≤ N := le_inf (map_subtype_le _) hKM
  have hKcomp : ((K.map H.subtype).subgroupOf N).IsCComponent :=
    (hKH.symm ▸ hK).subgroupOf_of_le hKN inf_le_left
  have hBKm : P.sixGroup ≤ K.map H.subtype := by
    intro x hx
    exact ⟨⟨x, P.sixGroup_le_coset_centralizer hc hx⟩, hBK hx, rfl⟩
  have he := (P.coset_local_component_central hc).eq_of_le hKcomp (comap_mono hBKm)
  apply le_antisymm ?_ hBKm
  intro x hx
  have hxN : (⟨x, hKN hx⟩ : N) ∈ P.sixGroup.subgroupOf N := by
    rw [he]
    exact hx
  exact hxN

/-- The remaining obstruction is an actual proper C.2.7 enlargement,
with the A₆ residual still a component of the literal intersection. -/
theorem coset_components_or_C27_enlargement_central
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models) :
    P.CosetComponents ∨ ∃ c ∈ P.fixed, ∃ K : Subgroup G,
      P.sixGroup < K ∧
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple
        (centralizer ({c * (P.six : G)} : Set G))
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K ∧
      centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G) ∧
      (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent := by
  classical
  by_cases hC : P.CosetComponents
  · exact Or.inl hC
  right
  have hbad : ∃ c ∈ P.fixed,
      ¬ (centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (P.sixGroup : Set G) ∧
        (P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G))).IsCComponent) := by
    by_contra! h
    exact hC ⟨fun c hc => (h c hc).1, fun c hc => (h c hc).2⟩
  obtain ⟨c,hc,hbad⟩ := hbad
  let H := centralizer ({c * (P.six : G)} : Set G)
  obtain ⟨K,hK,hn,hBK,hf,hq⟩ := P.coset_containing_component_quasisimple_central structural M hc
  let A := K.map H.subtype
  have hAH : A ≤ H := map_subtype_le _
  have hKA : A.subgroupOf H = K := comap_map_eq_self_of_injective H.subtype_injective K
  have hAc : (A.subgroupOf H).IsCComponent := hKA.symm ▸ hK
  have hAn : H ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAH).mp (hKA.symm ▸ hn)
  have hBA : P.sixGroup ≤ A := by
    intro x hx
    exact ⟨⟨x, P.sixGroup_le_coset_centralizer hc hx⟩, hBK hx, rfl⟩
  have hne : A ≠ P.sixGroup := by
    intro he
    exact hbad (he ▸ ⟨hAn,hAc⟩)
  have hout : ¬ A ≤ normalizer (L : Set G) := fun hh =>
    hne (P.coset_container_eq_of_le_local_central hc hK hBK hh)
  have hAf : generalizedFitting A = pCore 2 A := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2
      (K.equivMapOfInjective H.subtype H.subtype_injective)).mp
    rw [← hf]
    exact centralizer_generalizedFitting_le K
  have hAq : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _
      (K.equivMapOfInjective H.subtype H.subtype_injective) (pCore_map_iso 2 _))
  refine ⟨c,hc,A,lt_of_le_of_ne hBA (Ne.symm hne),
    ⟨P.coset_pushingUp_setup structural M hc,⟨hAH,hAc⟩,hAq,hAf,
      fun hh => hout (hh.trans inf_le_right),(P.coset_core_le hc).trans hAn⟩,hAn,?_⟩
  have hBN : P.sixGroup ≤ normalizer (L : Set G) ⊓ A :=
    le_inf ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer)) hBA
  exact (P.coset_local_component_central hc).subgroupOf_of_le hBN
    (le_inf (inf_le_right.trans hAH) inf_le_left)


open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
open scoped MatrixGroups

/-- No actual C.2.7 source component can properly enlarge the six-point
residual at any element of the fixed coset. -/
theorem coset_no_source_enlargement_central
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {c : G} (hc : c ∈ P.fixed) {K : Subgroup G} (hBK : P.sixGroup ≤ K)
    (h : Input KnownSimple.IsKnownSimple
      (centralizer ({c * (P.six : G)} : Set G))
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K)
    (hK : centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G)) : False := by
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let N := centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)
  have hB : P.sixGroup ≤ N ⊓ K := le_inf
    (le_inf (P.sixGroup_le_coset_centralizer hc)
      ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer))) hBK
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := (P.coset_sylow_le hc).trans hK
  have hTN : (T : Subgroup G) ≤ N := le_inf (P.coset_sylow_le hc)
    (S.hypothesis.source_sylow_normalizes structural)
  have hLR : L ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := le_sup_right.trans hLR
  have hBR : P.sixGroup ≤ normalizer (R : Set G) :=
    (pointResidual_le L (P.six : G)).trans (inf_le_left.trans (le_sup_left.trans hLR))
  have hF {F : ChapterB.QuasisimpleSource.BinaryField} (large : 1 < F.degree) :
      2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega))
  cases star_model_from_source h with
  | linearTwo F e => exact ChapterC.C27Source.CentralSix.no_linearTwo_star_of_six h hB P.sixRadicalEquiv e
  | linearThree F e => exact ChapterC.C27Source.CentralSix.no_linearThree_star_of_six h hB P.sixRadicalEquiv T hTK hTN F e
  | symplectic F large e => exact ChapterC.C27Source.CentralSix.no_symplectic_star_of_six h hB P.sixRadicalEquiv T hTK hTN (hF large) e
  | g2 F large e => exact ChapterC.C27Source.CentralSix.no_g2_star_of_six h hB P.sixRadicalEquiv T hTK hTN (hF large) e
  | g2DerivedTwo e => exact ChapterC.C27Source.CentralSix.no_binaryG2_star_of_six h hB P.sixRadicalEquiv e
  | alternating n hn e =>
    rcases hn with hn | hn | hn | hn
    · exact ChapterC.C27Source.CentralSix.no_small_alternating_star_of_six h hB P.sixRadicalEquiv (Or.inl hn) e
    · exact ChapterC.C27Source.CentralSix.no_small_alternating_star_of_six h hB P.sixRadicalEquiv (Or.inr hn) e
    · exact ChapterC.C27Source.CentralSix.no_large_alternating_star_of_six h hB P.sixRadicalEquiv hBR T hTK hTR (Or.inl hn) e
    · exact ChapterC.C27Source.CentralSix.no_large_alternating_star_of_six h hB P.sixRadicalEquiv hBR T hTK hTR (Or.inr hn) e
  | linearFiveTwo e =>
    exact ChapterC.C27Source.CentralSix.no_linearFive_star_of_normal_six h hB
      (inf_le_left.trans (P.coset_local_normalizes hc)) P.sixRadicalEquiv T hTK hTN e
  | tripleSix _ e => exact ChapterC.C27Source.CentralSix.no_tripleSix_star_of_six h hB P.sixRadicalEquiv e

/-- The six-point residual is a normal C-component in every literal
fixed-coset centralizer. Normality is relative to that centralizer. -/
theorem cosetComponents_of_central_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models) :
    P.CosetComponents := by
  rcases P.coset_components_or_C27_enlargement_central structural M with hc | ⟨c,hc,K,hBK,h,hK,_⟩
  · exact hc
  · exact (P.coset_no_source_enlargement_central structural hc hBK.le h hK).elim

end SylowNormalizer.Points
namespace Setup.NaturalCoordinates

/-- Source 12.3.6 without a separately chosen pair of central representatives. -/
theorem source_weight_six_centralizer (E : S.NaturalCoordinates)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (v : V) (hv : weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨P⟩ := SylowNormalizer.points_nonempty E structural
  apply E.centralizer_le_of_same_weight v P.six (hv.trans P.six_weight.symm)
  apply PointCentralizers.six_centralizer_le_of_normalizes P structural
  simpa only [one_mul] using
    (P.cosetComponents_of_central_source structural (P.sourceModels structural)).normalizes
      1 P.fixed.one_mem

end Setup.NaturalCoordinates
namespace PointCentralizers

/-- The source weight-six input, with both central-cover cases retained. -/
theorem source_sixInput (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) : SixInput P := by
  apply sixInput_of_normalizes P structural
  simpa only [one_mul] using
    (P.cosetComponents_of_central_source structural (P.sourceModels structural)).normalizes
      1 P.fixed.one_mem

/-- Source 12.3.6 for every weight-six vector, in the ambient group. -/
theorem source_six_centralizers (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (v : V) (hv : weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) :=
  E.centralizer_le_of_same_weight v P.six (hv.trans P.six_weight.symm)
    (six_centralizer_le P (source_sixInput P structural) structural)

/-- The weight-six premise of the shared 12.3.7 theorem is now discharged. -/
theorem source_1237 (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    Function.Surjective (E.sourceNormalizerModel structural).permutation ∧
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    P.five = ⁅P.five,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    omegaCenterIn ((P.five ⊔ (T : Subgroup G)).pCoreIn 2) =
      ⁅V,P.five⁆ ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) ∧
    Disjoint ⁅V,P.five⁆
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (P.five : Set G)) :=
  source_1237_of_sixInput P (source_sixInput P structural) structural escape

/-- The actual LocalAnalysis consumer now retains only the weight-two obligations. -/
noncomputable def localAnalysis_of_twoInput (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (B2 : TwoInput P) : S.LocalAnalysis :=
  localAnalysis P (source_sixInput P structural) B2 structural
    (E.sylow_normalizer_le_component structural)

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
