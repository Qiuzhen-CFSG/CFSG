module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherImageSieve
public import Theory.GroupTheory.CComponent.QuasisimpleLocalCore

/-!
# Intrinsic quotients of the containing component in higher rigidity

The literal map K → KR/R has a two-group kernel, so it induces the displayed
isomorphism K/O₂(K) ≃ (KR/R)/O₂(KR/R), with its representative equation.
The image of Y is quasisimple and local for the full image Sylow. Restricting
that Sylow to KR/R forces O₂(KR/R) into its center. Thus a binary-linear
intrinsic quotient of K is a central covering of exactly the kind handled
by the established non-enlargement theorem. Equality lifts to Y=K and feeds
the original residual-normality, rigidity and parabolic-complement consumer.

The maximal-component catalogue and exceptional quotient transport remain
with qt-d-12213-local-rigidity; this module proves the ordinary intrinsic
quotient branch, not the exhaustive containing-image list.
Source: Aschbacher–Smith, original 12.2.25–26, printed pp.805–806.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The map to the actual image of a containing subgroup in N(R)/R. -/
def containingImageMap {K : Subgroup G}
    (hKN : K ≤ normalizer (sectionRadical T U : Set G)) :
    K →* ThreeRigidity.image T U K :=
  ((quotient (sectionRadical T U)).subgroupMap
    (K.subgroupOf (normalizer (sectionRadical T U : Set G)))).comp
      (subgroupOfEquivOfLe hKN).symm.toMonoidHom

omit [Finite G] in
theorem containingImageMap_surjective {K : Subgroup G}
    (hKN : K ≤ normalizer (sectionRadical T U : Set G)) :
    Function.Surjective (containingImageMap hKN) :=
  ((quotient (sectionRadical T U)).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hKN).symm.surjective

omit [Finite G] in
theorem containingImageMap_ker_isPGroup {K : Subgroup G}
    (hKN : K ≤ normalizer (sectionRadical T U : Set G)) :
    IsPGroup 2 (containingImageMap hKN).ker := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  have he : (containingImageMap hKN).ker =
      ((quotient R).comp (inclusion hKN)).ker := by
    ext k
    change containingImageMap hKN k = 1 ↔ quotient R (inclusion hKN k) = 1
    exact ⟨fun hk => congrArg Subtype.val hk, fun hk => Subtype.ext hk⟩
  rw [he]
  change IsPGroup 2 (((QuotientGroup.mk' (R.subgroupOf N)).ker).comap (inclusion hKN))
  rw [QuotientGroup.ker_mk']
  exact (T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype.comap_of_injective
    (inclusion hKN) (inclusion_injective hKN)

/-- The intrinsic two-core quotients correspond under the literal image map. -/
def containingImageTwoCoreEquiv {K : Subgroup G}
    (hKN : K ≤ normalizer (sectionRadical T U : Set G)) :
    (K ⧸ pCore 2 K) ≃*
      (ThreeRigidity.image T U K ⧸ pCore 2 (ThreeRigidity.image T U K)) :=
  (containingImageMap hKN).pCoreQuotientEquiv
    (containingImageMap_surjective hKN) (containingImageMap_ker_isPGroup hKN)

theorem containingImageTwoCoreEquiv_apply {K : Subgroup G}
    (hKN : K ≤ normalizer (sectionRadical T U : Set G)) (k : K) :
    containingImageTwoCoreEquiv hKN (QuotientGroup.mk' (pCore 2 K) k) =
      QuotientGroup.mk' _ (containingImageMap hKN k) := rfl

/-- Quasisimplicity of the original smaller image forces the containing
image's intrinsic two-core to be central. -/
theorem containing_image_twoCore_central
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G}
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K) :
    pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let S : Sylow 2 (NormalizerQuotient R) :=
    (T.subtype (sylow_normalizes_sectionRadical C)).mapSurjective
      (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (R.subgroupOf N) := by
    let : Group.IsNilpotent (R.subgroupOf N) :=
      ((T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).comap_subtype).isNilpotent
    infer_instance
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let Kb := ThreeRigidity.image T U K
  have hKb : Kb.IsCComponent := hK.map_quotient (R.subgroupOf N)
  have hle : Yb ≤ Kb := map_mono (comap_mono hYK)
  let : IsQuasisimple Yb := residual_image_quasisimple h D structural A C B hd
  let : IsQuasisimple (Yb.subgroupOf Kb) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm
  obtain ⟨SK, _, hlocal⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    S (residual_image_local h D structural A C B hd) hle hKb.subnormal
  have htop : (⊤ : Subgroup Kb).IsCComponent := by
    simpa only [subgroupOf_self] using hKb.subgroupOf le_rfl
  exact twoCore_le_center_of_quasisimple_local_component htop SK (Yb.subgroupOf Kb) hlocal

/-- Binary linear intrinsic quotients of Y_R feed the existing image exclusion,
without identifying O₂(Y_R) with Y_R ∩ R. -/
theorem residual_eq_containing_of_binary_twoCore_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) m 2) :
    rigidityHyperplaneResidual L U V = K := by
  apply residual_eq_containing_of_binary_central_cover h D structural A C B hd hKN hK hYK
    (QuotientGroup.mk' (pCore 2 (ThreeRigidity.image T U K)))
    (QuotientGroup.mk'_surjective _) _ hm
    (hmodel.of_mulEquiv (containingImageTwoCoreEquiv hKN).symm)
  rw [QuotientGroup.ker_mk']
  exact containing_image_twoCore_central h D structural A C B hd hK hYK

/-- The actual intrinsic binary quotient yields residual normality and the
original rigidity and parabolic complement conclusions. -/
theorem source_rigidity_of_containing_binary_twoCore_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    {m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) m 2) :
    normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U := by
  have he := residual_eq_containing_of_binary_twoCore_quotient h D structural A C
    (RigidityKernel.source_centralizers h D structural A C hnone) hd hKN hK hYK hm hmodel
  have hnormal : normalizer (sectionRadical T U : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G) := by simpa only [he] using hn
  exact ⟨hnormal, source_rigidity_step_of_residual_normal h D structural A C hnone hd hnormal⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
