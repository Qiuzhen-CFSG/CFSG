module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuReduction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscapeAt

/-!
# Triple-Mathieu reduction at the original G,T

This replays the source 14.7.36 argument using only same-G,T earlier
structural and alternative results. The original groups, quotients and
actions are retained; no later 14.7.47 input is assumed.
Source: Aschbacher–Smith, printed p.1059, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section06.OddCriticalPair.Selection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem local_triple_mathieu_central_point_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let B := C.map q
    C.Normal ∧
      pCore 3 (HStar I) = ((F.Li L 1).subgroupOf I).map q ∧
      ((F.Li L 1).subgroupOf I).map q = (center B).map B.subtype ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      F.Li L 1 ≤ C.map I.subtype ∧
      ⁅F.UH I,F.Li L 1⁆ = F.UH I ∧ ⁅F.UH I,C.map I.subtype⁆ = F.UH I := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let Z := (center B).map B.subtype
  let A := (F.Li L 1).subgroupOf I
  let : IsQuasisimple (C ⧸ pCore 2 C) :=
    WholeResidualAssembly.GuardedSource.local_component_twoCore_isQuasisimple h hab structural previous faithful I hI C hC
  have hz : Nat.card (center (C ⧸ pCore 2 C)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Sporadic.Mathieu.M22TripleCover.center_card
  have hr : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by
    rw [primeRank_congr 3 e]
    exact Sporadic.Mathieu.M22TripleCover.two_le_threeRank
  have hIr : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  let hCn : C.Normal := hC.normal_of_cubic_core_center_threeRank hz.le hr hIr
  let : B.Normal := hCn.map q (QuotientGroup.mk'_surjective _)
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hc : Nat.card Z = 3 := by
    rw [card_map_of_injective B.subtype_injective,
      ←Nat.card_congr (centerCongr (cComponentTwoCoreQuotientEquiv hC)).toEquiv]
    exact hz
  have hZP : Z ≤ pCore 3 (HStar I) :=
    le_sSup ⟨inferInstance,IsPGroup.of_card (p := 3) (n := 1) (by simpa using hc)⟩
  have hZ : Z = pCore 3 (HStar I) := eq_of_le_of_card_ge hZP (by
    rw [hc]
    exact WholeResidualAssembly.GuardedSource.local_threeCore_card_le_three d h hab structural previous faithful earlier I hI)
  have hP : pCore 3 (HStar I) = A.map q :=
    (WholeResidualAssembly.GuardedSource.local_threeCore_eq_bot_or_point d h hab structural previous faithful earlier I hI).resolve_left
      (by intro he; rw [hZ,he,card_bot] at hc; norm_num at hc)
  have hAZ : A.map q = Z := hP.symm.trans hZ.symm
  have hAn : A.Normal := WholeResidualAssembly.GuardedSource.local_point_normal_of_star_normal h structural I
    (sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI))
    (hP ▸ (inferInstance : (pCore 3 (HStar I)).Normal))
  have hLI := F.Li_one_le_of_mem_Hz hI
  have hAp : IsPPerfect 2 A :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hLI).symm.toMonoidHom (subgroupOfEquivOfLe hLI).symm.surjective
  have hAC : A ≤ C := isPPerfect_le_of_map_le_of_kernel_normalizes q A C hAp
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (by rw [C.normalizer_eq_top]; exact le_top)
    (hAZ.le.trans (map_subtype_le _))
  have hLC : F.Li L 1 ≤ C.map I.subtype := by
    simpa only [A,map_subgroupOf_eq_of_le hLI] using map_mono (f := I.subtype) hAC
  have hnC : I ≤ normalizer (C.map I.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hCn
  let := h.chosen.elementary
  exact ⟨hCn,hP,hAZ,hAn,hLC,
    (conjugateSpanBy_eq_commutator_of_seed V I (F.Li L 1) (F.Li L 1) hLI
      ((normal_subgroupOf_iff_le_normalizer hLI).mp hAn) le_rfl (seed_commutator h F)).symm,
    (conjugateSpanBy_eq_commutator_of_seed V I (C.map I.subtype) (F.Li L 1)
      (map_subtype_le _) hnC hLC (seed_commutator h F)).symm⟩

theorem local_triple_mathieu_reduced_residual_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) :
    let J := C ⊔ (T : Subgroup G)
    let CJ := C.subgroupOf J
    let q := QuotientGroup.mk' (pCore 2 J)
    let B := CJ.map q
    J ≤ I ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
      CJ.IsCComponent ∧ CJ.Normal ∧
      (pResidual 2 J).map J.subtype = C ∧
      (q.comp CJ.subtype).ker = pCore 2 CJ ∧
      F.Li L 1 ≤ C ∧ ((F.Li L 1).subgroupOf J).Normal ∧
      ((F.Li L 1).subgroupOf J).map q = (center B).map B.subtype ∧
      ⁅F.UH J,F.Li L 1⁆ = F.UH J ∧ ⁅F.UH J,C⁆ = F.UH J := by
  let J := C ⊔ (T : Subgroup G)
  let a := subgroupOfEquivOfLe hCI
  let eI := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  obtain ⟨_,_,_,_,hLC,_,_⟩ := local_triple_mathieu_central_point_at
    d h hab structural previous faithful earlier I hI (C.subgroupOf I) hC eI
  rw [map_subgroupOf_eq_of_le hCI] at hLC
  have hJe : C ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = J := by
    rw [←sup_assoc,sup_eq_left.mpr hLC]
  have hCn : (C.subgroupOf I).Normal :=
    (local_triple_mathieu_central_point_at d h hab structural previous faithful earlier
      I hI (C.subgroupOf I) hC eI).1
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (F.sylow_le_of_mem_Hz hI).trans
      ((normal_subgroupOf_iff_le_normalizer hCI).mp hCn)
  have horbit : conjugateSpanBy ((C.subgroupOf I).map I.subtype) (T : Subgroup G) = C := by
    rw [map_subgroupOf_eq_of_le hCI]
    exact le_antisymm (conjugateSpanBy_le le_rfl hTC) (le_conjugateSpanBy _ _)
  have hJ : J ∈ F.Hz L (normalizer (L : Set G)) := by
    have hh := (local_component_reduced_mem_Hz_at h structural I hI (C.subgroupOf I) hC).2.2
    rw [horbit,hJe] at hh
    exact hh
  have hJI : J ≤ I := sup_le hCI (F.sylow_le_of_mem_Hz hI)
  have hCJ : (C.subgroupOf J).IsCComponent := hC.subgroupOf_of_le le_sup_left hJI
  let b := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let eJ := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  obtain ⟨hnJ,_,hz,hp,_,hmP,hmC⟩ := local_triple_mathieu_central_point_at
    d h hab structural previous faithful earlier J hJ (C.subgroupOf J) hCJ eJ
  let := hnJ
  let := hCJ.perfect
  have hperfect : IsPPerfect 2 (C.subgroupOf J) :=
    (pResidual_eq_top_iff 2 _).mp (pResidual_eq_top_of_isPerfect 2)
  have hgen : C.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show C ≤ J from le_sup_left) (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hr : pResidual 2 J = C.subgroupOf J := pResidual_eq_of_isPPerfect_sup _ _
    hperfect T.isPGroup'.comap_subtype hgen
  refine ⟨hJI,hJ,hCJ,hnJ,?_,?_,hLC,hp,hz,hmP,?_⟩
  · rw [hr,map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left)]
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hCJ.subnormal).symm
  · simpa only [map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left)] using hmC

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt
