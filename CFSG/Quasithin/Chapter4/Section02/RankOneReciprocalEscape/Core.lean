module
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import CFSG.Quasithin.ChapterC.Section02
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# The reversed maximal-local pushing-up setup

When the generalized-Fitting preimage of an outside maximal two-local H is
contained in M, A.4.4 identifies O₂(H) with O₂(H∩M). Maximality of H controls
the characteristic normalizers of this core. Restricting that control to M
proves radicality and constructs the actual reversed C.2.3 setup, including
its normal-closure Sylow clause. Its radical contains O₂(M), and A.4.4 forces
the opposite generalized-Fitting preimage to escape H.

Source: Aschbacher--Smith, the paragraph following 4.2.6 and A.4.4,
printed pp.609,58. This is the reciprocal preparation, not yet 4.2.5.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open ChapterA.Section04 Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem maximal_core_control {H : Subgroup G} (hH : IsMaximalTwoLocal H) :
    H.pCoreIn 2 ≠ ⊥ ∧ normalizer (H.pCoreIn 2 : Set G) = H ∧
      (H.pCoreIn 2).characteristicNormalizerClosure ≤ H := by
  have hne := Chapter1.mem_H_of_isTwoLocal hH.1
  have hnorm : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  refine ⟨hne, (hH.eq_of_le ⟨_,hne,isPGroup_pCoreIn 2 H,rfl⟩ hnorm).symm, ?_⟩
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hC hCne
  let := hC
  have hm : C.map (H.pCoreIn 2).subtype ≠ ⊥ := fun he =>
    hCne ((map_eq_bot_iff_of_injective _ (H.pCoreIn 2).subtype_injective).mp he)
  exact hH.2 ⟨_,hm,((isPGroup_pCoreIn 2 H).to_subgroup C).map _,rfl⟩
    (hnorm.trans (normalizer_le_normalizer_characteristic_image _ C))

/-- The actual reversed C.2.3 setup, with its core comparison and reverse escape. -/
theorem reciprocal_setup {κ : GroupClass} {H M : Subgroup G}
    (hH : IsMaximalTwoLocal H) (hM : IsMaximalTwoLocal M)
    (hs : IsSQTK κ M) (hne : H ≠ M)
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    H.pCoreIn 2 = (H ⊓ M).pCoreIn 2 ∧
      PushingUpSetup κ M (H.pCoreIn 2) (H ⊓ M) ∧
      M.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      ¬ (generalizedFitting (M ⧸ pCore 2 M)).comap
        (QuotientGroup.mk' (pCore 2 M)) ≤ H.subgroupOf M := by
  have hpre : twoGeneralizedFittingPreimage H ≤ H ⊓ M :=
    le_inf (map_subtype_le _) (map_le_iff_le_comap.mpr hf)
  have hX : IntersectionAlternative
      (twoCoreQuotientImage H (twoGeneralizedFittingPreimage H)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl, ?_, ?_⟩
    · exact (inferInstance : ((generalizedFitting (H ⧸ pCore 2 H)).subgroupOf
        (generalizedFitting (H ⧸ pCore 2 H))).Normal).isSubnormal
    · apply (closure_le _).mpr
      intro x hx
      exact hx.1.1
  have hc := lemma_A_4_4_1 H M _ (twoCore_le_fittingPreimage H) hpre hX
  have hQM : H.pCoreIn 2 ≤ M := (twoCore_le_fittingPreimage H).trans (hpre.trans inf_le_right)
  have hQA : H.pCoreIn 2 ≤ H ⊓ M := (twoCore_le_fittingPreimage H).trans hpre
  obtain ⟨hQne,hQN,hQC⟩ := maximal_core_control hH
  have hr : IsPRadical 2 ((H.pCoreIn 2).subgroupOf M) := by
    refine ⟨?_, ?_⟩
    · intro hb
      apply hQne
      simpa only [map_subgroupOf_eq_of_le hQM, Subgroup.map_bot] using
        congrArg (map M.subtype) hb
    · apply map_injective M.subtype_injective
      change ((normalizer ((H.pCoreIn 2).subgroupOf M : Set M)).pCoreIn 2).map M.subtype = _
      rw [map_pCoreIn_of_injective 2 _ M.subtype M.subtype_injective,
        ← subgroupOf_normalizer_eq hQM, subgroupOf_map_subtype, hQN,
        map_subgroupOf_eq_of_le hQM]
      exact hc.symm
  have hcontrol : ((H.pCoreIn 2).subgroupOf M).characteristicNormalizerClosure ≤
      (H ⊓ M).subgroupOf M := by
    intro x hx
    exact ⟨characteristicNormalizerClosure_subgroupOf_le hQM hQC hx, x.property⟩
  have hnormal : ((H.pCoreIn 2).subgroupOf (H ⊓ M)).Normal := by
    rw [hc]
    exact normal_subgroupOf_of_le_normalizer
      ((H ⊓ M).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (H ⊓ M : Subgroup G))))
  have hclosure : (normalClosure ((H.pCoreIn 2).subgroupOf (H ⊓ M) : Set (H ⊓ M : Subgroup G))).map
      (H ⊓ M).subtype = H.pCoreIn 2 := by
    let := hnormal
    rw [normalClosure_eq_self, map_subgroupOf_eq_of_le hQA]
  have hcore : M.pCoreIn 2 ≤ H.pCoreIn 2 := by
    have hh := ChapterC.twoCore_le_radical _ hr.isPGroup hr.2
    have hm := map_mono (f := M.subtype) hh
    rwa [map_subgroupOf_eq_of_le hQM] at hm
  refine ⟨hc, ⟨hs,hQM,inf_le_right,hr,hcontrol,?_⟩, hcore, ?_⟩
  · rw [hclosure]
    exact Chapter1.isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 H,le_rfl,
      fun U _ hu hu' => le_antisymm hu' hu⟩
  · intro hh
    exact hne (lemma_A_4_4_3 H M _ (twoCore_le_fittingPreimage H) hpre hX hH hM
      (map_le_iff_le_comap.mpr hh))
end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
