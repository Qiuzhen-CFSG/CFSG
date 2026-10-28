module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.SourceBorel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SevenNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceBound
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The original mixed A₅–S₃ amalgam

The actual component K of G₁ and the G₂-normal closure I₂ of O₂(G₁)
satisfy F.1.1 in the zero-core branch. Normality of the original point
residual gives the S₃ quotient of I₂. The actual component Borel preserves
the original plane, so the two parabolics lie in G₁ and G₂ and inherit
characteristic two. All Sylow intersections and subgroup inclusions are
the original ones.

The mixed rank-two bound gives |T| ≤ 1024. The source tensor lower bound
is a later step. Universal earlier inputs used by the existing component
normality and Borel producers remain explicit; this is not a same-G,T
completion of 14.7.47.

Source: Aschbacher–Smith 14.7.46, printed p.1063; F.1.1 and F.1.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
open Chapter12.Section08 Chapter12.Section09.NaturalSource CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

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

omit [Finite G] in
/-- Mapping the intrinsic component Borel gives exactly F.1.1's ambient Borel. -/
theorem componentSylowNormalizer_eq_borel (I : Subgroup G) (C : Subgroup I) :
    componentSylowNormalizer T I C = ChapterF.Source.borel (C.map I.subtype) (T : Subgroup G) := by
  let K := C.map I.subtype
  have hK : K ≤ I := map_subtype_le _
  have hKC : K.subgroupOf I = C := comap_map_eq_self_of_injective I.subtype_injective C
  have hi : (((T : Subgroup G) ⊓ K).subgroupOf I) = (T : Subgroup G).subgroupOf I ⊓ C := by
    change ((T : Subgroup G) ⊓ K).comap I.subtype = _
    rw [comap_inf]
    change (T : Subgroup G).subgroupOf I ⊓ K.subgroupOf I = _
    rw [hKC]
  have hn : (normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).subgroupOf I =
      normalizer (((T : Subgroup G).subgroupOf I ⊓ C : Subgroup I) : Set I) := by
    rw [subgroupOf_normalizer_eq (inf_le_right.trans hK), hi]
  have hb : (ChapterF.Source.borel K (T : Subgroup G)).subgroupOf I =
      C ⊓ normalizer (((T : Subgroup G).subgroupOf I ⊓ C : Subgroup I) : Set I) := by
    change (K ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).subgroupOf I = _
    change (K ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).comap I.subtype = _
    rw [comap_inf]
    change K.subgroupOf I ⊓
      (normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).subgroupOf I = _
    rw [hKC,hn]
  have hh := congrArg (Subgroup.map I.subtype) hb
  rw [map_subgroupOf_eq_of_le (show ChapterF.Source.borel K (T : Subgroup G) ≤ I from
    inf_le_left.trans hK)] at hh
  exact hh.symm

/-- F.1.1 on the actual original component, plane core closure and Sylow.
Only source normal-point and zero-core premises are added to the original row. -/
theorem original_mixed_amalgam
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hpoint : ((F.Li L 1).subgroupOf F.H).Normal)
    (hcore : pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥) :
    ChapterF.Source.HypothesisF11 ![C.map F.H.subtype, planeCoreClosure F] (T : Subgroup G) := by
  let K := C.map F.H.subtype
  let R := planeCoreClosure F
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  have hKH : K ≤ F.H := map_subtype_le _
  have hC' : (K.subgroupOf F.H).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hC
  have hKn := local_cComponent_normal d h hab structural previous faithful earlier
    F.H K hH hKH hC'
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (F.invariant 2).trans (le_normalizer_conjugateSpanBy _ _)
  have hsK := sylow_intersection K hTK
  have hsR := sylow_intersection R hTR
  obtain ⟨_,⟨eR⟩⟩ := planeCoreClosure_quotient_at h (structural.at T)
    (plane_moved_of_point_normal_at h (structural.at T) hpoint)
  let cK := C.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ cK (pCore_map_iso 2 cK)).symm.trans e
  have hBR : ChapterF.Source.borel R (T : Subgroup G) = (T : Subgroup G) ⊓ R := by
    convert ChapterF.Source.borel_eq_of_cubic_local_sylow R ((T : Subgroup G) ⊓ R) hsR eR using 1
    simp only [ChapterF.Source.borel, inf_assoc, inf_idem]
  obtain ⟨hBG,hBN⟩ := local_component_borel_normalizes_plane_core d h hab structural
    previous faithful earlier F.H hH C hC hout
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

/-- The actual original zero-core branch has a Sylow subgroup of order at most
1024; no supplied F.1.1 package or recognition callback is used. -/
theorem original_mixed_zero_core_sylow_card_le
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hout : ¬ F.Li L 1 ≤ C.map F.H.subtype)
    (hpoint : ((F.Li L 1).subgroupOf F.H).Normal)
    (hcore : pCore 2 (C.map F.H.subtype ⊔ planeCoreClosure F ⊔ (T : Subgroup G) : Subgroup G) = ⊥) :
    Nat.card T ≤ 1024 := by
  have hF := original_mixed_amalgam d h hab structural previous faithful earlier C hC e hout hpoint hcore
  let cK := C.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let eK := (QuotientGroup.congr _ _ cK (pCore_map_iso 2 cK)).symm.trans e
  have hR := (planeCoreClosure_quotient_at h (structural.at T)
    (plane_moved_of_point_normal_at h (structural.at T) hpoint)).2
  exact ChapterF.Source.MixedDGS.mixed_a5_s3_sylow_card_le_1024 hF ⟨eK⟩ hR

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment
