module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.Size
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.Borel

/-!
# The original mixed zero-core exclusion at the same group and Sylow

The actual component Sylow normalizer preserves the original plane by the
same-G,T Borel residual calculation. This constructs F.1.1 on the literal
component and plane core closure, and gives the bound |T| ≤ 1024 in the
zero-core branch. The actual section of dimension at least eight gives
|T| ≥ 2048, so the generated group has nonzero two-core.

Component normality, original plane movement and the original section's
dimension remain explicit. The original point-normality interfaces specialize
the movement-premise declarations. No universal structural or previous-theorem
input is reconstructed from its local specialization.
Source: Aschbacher–Smith 14.7.42,46, printed pp.1061–1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.At
open Chapter12.Section08 Chapter12.Section09.NaturalSource CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open OutsideProjectiveAt
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original Borel lies in the original plane normalizer and normalizes
the actual plane core closure. All Borel and seed data come from the source. -/
theorem local_component_borel_normalizes_plane_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    componentSylowNormalizer T I C ≤ F.Gi 2 ∧
      componentSylowNormalizer T I C ≤ normalizer (planeCoreClosure F : Set G) := by
  let B₀ := componentSylowNormalizer T I C
  obtain ⟨_,_,hBn,_⟩ := component_borel_of_not_contains_point_at
    d h hab structural previous faithful earlier I hI C hout
  obtain ⟨hseed,_⟩ := component_borel_fixed_actions_at
    d h hab structural previous faithful earlier I hI C hout
  have hBT : B₀ ≤ (pResidual 2 B₀).map B₀.subtype ⊔ (T : Subgroup G) :=
    le_embedded_pResidual_sup_sylow_of_normalizes T B₀ (le_sup_right.trans hBn)
  have hBG : B₀ ≤ F.Gi 2 := hBT.trans (sup_le
    (hseed.trans ((centralizer_le (F.le_seed 2)).trans (Subgroup.centralizer_le_normalizer _)))
    (F.invariant 2))
  exact ⟨hBG, hBG.trans (le_normalizer_conjugateSpanBy _ _)⟩

private theorem rankOne_of_a5 {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : ChapterF.Source.IsRankOneModel X := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact .linear 2 (by decide) ⟨GaloisField 2 2, inferInstance, inferInstance,
    by simpa using hc, ⟨e.trans f.symm⟩⟩

private theorem rankOne_of_s3 {X : Type*} [Group X]
    (e : X ≃* Equiv.Perm (Fin 3)) : ChapterF.Source.IsRankOneModel X := by
  apply ChapterF.Source.IsRankOneModel.linear 1 (by decide)
  refine ⟨ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
  exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
    (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))⟩

private theorem sylow_intersection (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ K) K := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  exact ⟨P, by rw [hP, subgroupOf_map_subtype]⟩

/-- F.1.1 on the actual original component, plane core closure and Sylow.
The original plane movement and zero-core premises complete the original row. -/
theorem original_mixed_amalgam_of_plane_moved
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (hcore : pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥) :
    ChapterF.Source.HypothesisF11 ![C.map F.H.subtype, planeCoreClosure F] (T : Subgroup G) := by
  let K := C.map F.H.subtype
  let R := planeCoreClosure F
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  have hKH : K ≤ F.H := map_subtype_le _
  have hKn : (K.subgroupOf F.H).Normal := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective]
      using (inferInstance : C.Normal)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (F.invariant 2).trans (le_normalizer_conjugateSpanBy _ _)
  have hsK := sylow_intersection K hTK
  have hsR := sylow_intersection R hTR
  obtain ⟨_,⟨eR⟩⟩ := planeCoreClosure_quotient_at h structural hm
  let cK := C.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ cK (pCore_map_iso 2 cK)).symm.trans e
  have hBR : ChapterF.Source.borel R (T : Subgroup G) = (T : Subgroup G) ⊓ R := by
    convert ChapterF.Source.borel_eq_of_cubic_local_sylow R ((T : Subgroup G) ⊓ R) hsR eR using 1
    simp only [ChapterF.Source.borel, inf_assoc, inf_idem]
  obtain ⟨hBG,hBN⟩ := local_component_borel_normalizes_plane_core d h hab structural
    previous faithful earlier F.H hH C hout
  rw [componentSylowNormalizer_eq_borel] at hBG hBN
  have hGi (i : ℕ) (hi : i = 1 ∨ i = 2) : F.Gi i ∈ Chapter1.He G := by
    apply Chapter1.twoLocal_mem_He_of_sylow_le T (d.qtke.evenCharacteristic T) ?_ (F.invariant i)
    refine ⟨F.Vi i, ?_, ?_, rfl⟩
    · rcases hi with rfl | rfl
      · intro he
        have hc := F.card 1 (by decide)
        rw [he,card_bot] at hc
        norm_num at hc
      · intro he
        have hc := F.card 2 (by decide)
        rw [he,card_bot] at hc
        norm_num at hc
    · rcases hi with rfl | rfl
      · exact IsPGroup.of_card (n := 1) (by simpa using F.card 1 (by decide))
      · exact IsPGroup.of_card (n := 2) (by simpa using F.card 2 (by decide))
  refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,hcore,?_⟩
  · intro i; fin_cases i
    · exact hTK
    · exact hTR
  · intro i; fin_cases i
    · exact hsK
    · exact hsR
  · intro i; fin_cases i
    · exact rankOne_of_a5 eK
    · exact rankOne_of_s3 eR
  · intro i; fin_cases i
    · change ChapterF.Source.borel R (T : Subgroup G) ≤ _
      rw [hBR]
      exact inf_le_left.trans hTK
    · exact hBN
  · intro i; fin_cases i
    · change generalizedFitting (K ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel R (T : Subgroup G) : Subgroup G) =
        pCore 2 (K ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel R (T : Subgroup G) : Subgroup G)
      rw [hBR,sup_eq_left.mpr (show (T : Subgroup G) ⊓ R ≤ K ⊔ (T : Subgroup G) from
        inf_le_left.trans le_sup_right)]
      exact generalizedFitting_eq_pCore_of_sylow_overgroup T _ F.H le_sup_right
        (sup_le hKH (F.invariant 1)) (Chapter1.mem_He_iff.mp (hGi 1 (Or.inl rfl)))
    · change generalizedFitting (R ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel K (T : Subgroup G) : Subgroup G) =
        pCore 2 (R ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel K (T : Subgroup G) : Subgroup G)
      exact generalizedFitting_eq_pCore_of_sylow_overgroup T _ (F.Gi 2)
        (le_sup_right.trans le_sup_left)
        (sup_le (sup_le ((planeCoreClosure_le_parabolic h F).trans
          (F.P_le_G₂ (by decide) L h.chosen.normalizes)) (F.invariant 2)) hBG)
        (Chapter1.mem_He_iff.mp (hGi 2 (Or.inr rfl)))

/-- The normal-point specialization of the preceding plane-movement theorem. -/
theorem original_mixed_amalgam
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hpoint : ((F.Li L 1).subgroupOf F.H).Normal)
    (hcore : pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥) :
    ChapterF.Source.HypothesisF11 ![C.map F.H.subtype, planeCoreClosure F] (T : Subgroup G) := by
  exact original_mixed_amalgam_of_plane_moved d h hab structural previous faithful earlier C e hout
    (plane_moved_of_point_normal_at h structural hpoint) hcore

/-- The actual original zero-core branch has a Sylow subgroup of order at most
1024; no supplied F.1.1 package or recognition callback is used. -/
theorem original_mixed_zero_core_sylow_card_le_of_plane_moved
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (hcore : pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥) :
    Nat.card T ≤ 1024 := by
  have hF := original_mixed_amalgam_of_plane_moved d h hab structural previous faithful earlier C e hout hm hcore
  let cK := C.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let eK := (QuotientGroup.congr _ _ cK (pCore_map_iso 2 cK)).symm.trans e
  have hR := (planeCoreClosure_quotient_at h structural hm).2
  exact ChapterF.Source.MixedDGS.mixed_a5_s3_sylow_card_le_1024 hF ⟨eK⟩ hR

/-- The normal-point specialization of the preceding plane-movement theorem. -/
theorem original_mixed_zero_core_sylow_card_le
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hpoint : ((F.Li L 1).subgroupOf F.H).Normal)
    (hcore : pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥) :
    Nat.card T ≤ 1024 := by
  exact original_mixed_zero_core_sylow_card_le_of_plane_moved d h hab structural previous faithful earlier C e hout
    (plane_moved_of_point_normal_at h structural hpoint) hcore

variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- The exact original rank-eight section rules out zero core in the generated
mixed pair. The remaining module-classification premise is only its dimension. -/
theorem original_mixed_core_ne_bot_of_section_rank_of_plane_moved
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) F.H W)
    (s : BinaryConjugationSection F.H (F.UH F.H) (F.Vi 1) ρ)
    (hdim : 8 ≤ Module.finrank (ZMod 2) W) :
    pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
  intro hcore
  have hu := original_mixed_zero_core_sylow_card_le_of_plane_moved d h hab structural previous faithful
    earlier C e hout hm hcore
  have hl := sylow_card_ge_2048_of_local_section_rank_at h hab structural
    (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) ρ s hdim
  omega

/-- The normal-point specialization of the preceding plane-movement theorem. -/
theorem original_mixed_core_ne_bot_of_section_rank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hpoint : ((F.Li L 1).subgroupOf F.H).Normal)
    (ρ : Representation (ZMod 2) F.H W)
    (s : BinaryConjugationSection F.H (F.UH F.H) (F.Vi 1) ρ)
    (hdim : 8 ≤ Module.finrank (ZMod 2) W) :
    pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
  exact original_mixed_core_ne_bot_of_section_rank_of_plane_moved d h hab structural previous faithful earlier C e hout
    (plane_moved_of_point_normal_at h structural hpoint) ρ s hdim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.At
