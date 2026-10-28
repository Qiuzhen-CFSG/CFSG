module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalComponents
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreConclusion
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.GroupTheory.CComponent.CubicCenterRankNormal
public import Theory.Mathieu.M22.TripleCover.CubicFacts
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Central cubic and residual reduction for the Mathieu triple cover

In an original local, a triple-cover component is normal by its cubic
center and three-rank. Its embedded center has order three and therefore
exhausts the bounded three-core. The proved 14.7.27 alternative identifies
this center with the literal point image. Point normality and containment
lift through the actual two-core, using the point's two-perfectness.

Consequently the reduced local C L₁ T is C T, and C is its whole two-residual.
Both C and L₁ move the entire original local span. The full-point application
also constructs the same central cubic acting fixed-free on every literal
U/V₁ section, with its quadratic scalar polynomial. No irreducibility or
module recognition is assumed in that assertion.

These establish the central-cubic and full-movement steps of the triple-cover
branch. The degree-twelve recognition, Sylow fixed line and escaping solvable
overgroup needed for the contradiction remain. The retained earlier universal
structural hypotheses still require their same-G,T guarded successors for the
final source assembly.

Source: Aschbacher–Smith, 14.7.36, printed p.1059, using 14.7.27–28 and
14.7.5(5); refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual triple-cover center equals the original point image in the
literal local quotient. Normality and containment lift before either full
commutator equality is derived. -/
theorem local_triple_mathieu_central_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    local_component_twoCore_isQuasisimple h hab structural previous faithful I hI C hC
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
    exact local_threeCore_card_le_three d h hab structural previous faithful earlier I hI)
  have hP : pCore 3 (HStar I) = A.map q :=
    (local_threeCore_eq_bot_or_point d h hab structural previous faithful earlier I hI).resolve_left
      (by intro he; rw [hZ,he,card_bot] at hc; norm_num at hc)
  have hAZ : A.map q = Z := hP.symm.trans hZ.symm
  have hAn : A.Normal := local_point_normal_of_star_normal h structural I
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


/-- In the triple-cover branch, the source reduction is literally C T:
the point residual is already in C. The whole two-residual of this reduced
local is C, with its intrinsic two-core and full point/component movement. -/
theorem local_triple_mathieu_reduced_residual
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨_,_,_,_,hLC,_,_⟩ := local_triple_mathieu_central_point
    d h hab structural previous faithful earlier I hI (C.subgroupOf I) hC eI
  rw [map_subgroupOf_eq_of_le hCI] at hLC
  have hJe : C ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = J := by
    rw [←sup_assoc,sup_eq_left.mpr hLC]
  have hJ : J ∈ F.Hz L (normalizer (L : Set G)) := by
    rw [←hJe]
    exact (local_component_sylow_normalized_and_mem_Hz d h hab structural previous
      faithful earlier I C hI hCI hC).2
  have hJI : J ≤ I := sup_le hCI (F.sylow_le_of_mem_Hz hI)
  have hCJ : (C.subgroupOf J).IsCComponent := hC.subgroupOf_of_le le_sup_left hJI
  let b := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let eJ := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  obtain ⟨hnJ,_,hz,hp,_,hmP,hmC⟩ := local_triple_mathieu_central_point
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

/-- Application to the actual original point normalizer and its selected
component. This prepares the same C T and U_(C T) used in the triple-cover
module contradiction of 14.7.36. -/
theorem original_triple_mathieu_reduced_residual
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) :
    let D := C.map F.H.subtype
    let J := D ⊔ (T : Subgroup G)
    let DJ := D.subgroupOf J
    let q := QuotientGroup.mk' (pCore 2 J)
    let B := DJ.map q
    J ≤ F.H ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
      DJ.IsCComponent ∧ DJ.Normal ∧
      (pResidual 2 J).map J.subtype = D ∧
      (q.comp DJ.subtype).ker = pCore 2 DJ ∧
      F.Li L 1 ≤ D ∧ ((F.Li L 1).subgroupOf J).Normal ∧
      ((F.Li L 1).subgroupOf J).map q = (center B).map B.subtype ∧
      ⁅F.UH J,F.Li L 1⁆ = F.UH J ∧ ⁅F.UH J,D⁆ = F.UH J := by
  let D := C.map F.H.subtype
  have hD : (D.subgroupOf F.H).IsCComponent := by
    simpa only [D,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hC
  let a := equivMapOfInjective C F.H.subtype F.H.subtype_injective
  let eD := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans e
  exact local_triple_mathieu_reduced_residual d h hab structural previous faithful earlier
    F.H D (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) (map_subtype_le _) hD eD


/-- The central cubic of a hypothetical original triple-cover component is
fixed-free on every literal U/V₁ section and supplies the F₄ polynomial on
that whole section, before irreducible-module recognition. -/
theorem original_triple_mathieu_fixedFree_scalar
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : Representation.BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (hσ : σ.comp (starMap F) = ρ) :
    ∃ z : HStar F.H, orderOf z = 3 ∧
      zpowers z = star F (F.Li L 1) ∧
      zpowers z = (center (C.map (starMap F))).map (C.map (starMap F)).subtype ∧
      (∀ v, σ z v = v → v = 0) ∧ σ z ^ 2 + σ z + 1 = 0 := by
  obtain ⟨_,_,hc,hn,_,_,_⟩ := local_triple_mathieu_central_point
    d h hab structural previous faithful earlier F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) C hC e
  obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
  refine ⟨z,hz,hgen,hgen.trans hc,hfree,?_⟩
  apply Representation.RankTwo.quadratic_of_cubic_fixed_free (σ z) _ hfree
  rw [←map_pow,show z ^ 3 = 1 from by simpa only [hz] using pow_orderOf_eq_one z,map_one]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
