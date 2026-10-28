module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Supplement
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognition
public import Theory.SpecificGroups.PSL3Four.ThreeRank
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# The selected terminal residual and parabolic incidence

For the H-star subgroup selected inside the original quotient-centralizer
supplement XT, the literal Hall subgroup of H∩M has order three. The E.2
recognition leaves A₅ or a PSL₃(4) source image. The latter has three-rank
at least two, whereas cyclic Sylow three-subgroups of H bound every quotient
and subgroup by one. This argument retains the full source kernel.

Thus the original embedded K=O²(H) has K/O₂(K) isomorphic to A₅. The final
application selects this same H and supplies M₁≤L₁H from its original cubic
Hall subgroup. KernelCorank and Completion discharge the subsequent corank
and action-kernel steps. Point escape remains with qt-d-1251-source.
Source: Aschbacher--Smith, proof of 12.5.1, printed pp.821--822.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE ChapterB
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

/-- The chosen supplement H has the literal A₅ residual quotient. -/
theorem HStar_in_pointSupplement_residual_a5 {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5)) := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    change H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (Chapter3.Section02.localOrbit T L : Set G))
    simpa only [D.localOrbit_eq, ExteriorMarking.M] using hH
  have hlarge := (s.exteriorFusion_from_source h structural).generation_gt_one H hH
  let hP := Chapter10.source_hstar_minimal_parabolic_of_generation_gt_one F hH' hlarge
  have hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H := by
    have he := Chapter10.source_hstar_parabolicMax_eq_overlap F hH' hP
    change _ = (normalizer (Chapter3.Section02.localOrbit T L : Set G)).subgroupOf H at he
    simpa only [D.localOrbit_eq, ExteriorMarking.M] using he
  have hHG : H ≤ s.marking.Gi 1 := hHX.trans
    (sup_le s.pointSupplement_le_point s.sylow_le_G₁)
  obtain ⟨_,C,hC,hCH,hHall,hC3⟩ :=
    (s.exteriorFusion_from_source h structural).generation_two_hall_three H hH hHG
  have hc := s.pointSupplement_HStar_hall_card_three h structural hHX hC hCH hC3
  have hsize : ∀ n : ℕ, Odd n →
      n ∣ Nat.card (minimalParabolicMax (T.subtype hH.1.1.2) hP) → n ∣ 3 := by
    intro n hn hd
    have he : Nat.card (s.marking.M.subgroupOf H) = Nat.card (H ⊓ s.marking.M : Subgroup G) := by
      rw [←card_map_of_injective H.subtype_injective,subgroupOf_map_subtype,inf_comm]
    rw [hmax,he] at hd
    exact Chapter10.SourceOldResidual.odd_dvd_maximal_dvd_three hCH hHall hc hn hd
  rcases Chapter10.SourceOldResidual.residual_a5_or_linear_three_four
    (Chapter3.sqtk_of_mem_H F.simpleQTKE hH'.1.1.1) (T.subtype hH.1.1.2) hP hlarge hsize
    with ha | ⟨_,_,hlin⟩
  · exact ha
  · let S : Sylow 3 H := Classical.choice inferInstance
    have hr := s.HStar_in_pointSupplement_three_rank_le_one h structural hHX
    have hcyc := S.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
    let M := minimalParabolicMax (T.subtype hH.1.1.2) hP
    have hrq := S.primeRank_quotient_le_one hcyc (sourceKernel M)
    have hrs : primeRank 3 (sourceImage M (pResidual 2 H)) ≤ 1 :=
      (primeRank_subgroup_le 3 _).trans hrq
    obtain ⟨F₀,hF₀,hfin,hcard,⟨e⟩⟩ := hlin
    let := Fintype.ofFinite F₀
    let := Fintype.ofFinite Matrix.PSL3Four.F
    let eF : F₀ ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
      (by rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hcard,Matrix.PSL3Four.card_F])
    rw [primeRank_congr 3 (e.trans (Atlas.fieldEquivPSL 3 eF))] at hrs
    exact (Nat.not_succ_le_self 1 (Matrix.PSL3Four.ThreeRank.three_rank_ge_two.trans hrs)).elim

/-- Transport the recognition to the source's embedded K=O²(H). -/
theorem HStar_in_pointSupplement_embedded_residual_a5 {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    Nonempty (((pResidual 2 H).map H.subtype ⧸ pCore 2 ((pResidual 2 H).map H.subtype)) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := s.HStar_in_pointSupplement_residual_a5 h structural hH hHX
  let f := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  exact ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm.trans e⟩

/-- Apply recognition and parabolic incidence to the actual selected H. -/
theorem exists_pointSupplement_HStar_with_a5_and_incidence
    (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ s.pointSupplement ⊔ (T : Subgroup G) ∧ H ≤ s.marking.Gi 1 ∧
      s.marking.Mi 1 ≤ s.marking.Li 1 ⊔ H ∧
      Nonempty (((pResidual 2 H).map H.subtype ⧸ pCore 2 ((pResidual 2 H).map H.subtype)) ≃*
        alternatingGroup (Fin 5)) := by
  obtain ⟨H,hH,hHX,hHG⟩ := s.exists_HStar_in_pointSupplement h structural hout
  exact ⟨H,hH,hHX,hHG,s.point_parabolic_le_residual_sup_HStar h structural hH hHX,
    s.HStar_in_pointSupplement_embedded_residual_a5 h structural hH hHX⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
