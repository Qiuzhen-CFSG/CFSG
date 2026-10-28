module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionAugmentation
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionMoved
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionPointQuotient

/-!
# LocalAnalysisNaturalFourExclusionAugmentation at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionAugmentation`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

open ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem four_augmentation_false_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (K W : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K)
    (hV : V ≤ W) (hKW : K ≤ normalizer (W : Set G))
    (hzK : z ∈ centralizer (K : Set G))
    (π : K →* alternatingGroup (Fin 8)) (hπ : Function.Surjective π)
    (E : W ≃* Multiplicative (BinaryPermutation.core (Fin 8)))
    (ha : ∀ (k : K) (v w : W), (w : G) = (k : G) * (v : G) * (k : G)⁻¹ →
      (E w).toAdd = BinaryPermutation.alternatingCoreRepresentation (Fin 8) (π k) (E v).toAdd) :
    False := by
  let := S.chosen.elementary
  let := S.four_overcomponent_quasisimple_at structural e hd hz hz1 hzT hK hDK
  obtain ⟨hdim,hone,hw,_⟩ := S.four_augmentation_code e hd hz hz1 hDK hV hzK π hπ E ha
  exact BinaryPermutation.EightCore.normalizer_core_not_centralizes K V W hV hKW
    π hπ (AlternatingEight.quotient_cover_kernel_isTwoGroup π hπ) E ha hdim hone hw
    (S.four_overcomponent_moduleNormalizer_core_centralizes_at structural e hd hz hz1 hzT hK hDK)

theorem four_enlargement_eight_false_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (K : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K)
    (hCJ : starImage K (S.fourComponentPointCore z) K ≤
      offenderSubgroup (starRepresentation K (S.fourComponentPointCore z)))
    (c : ChapterC.C27Source.NonsplitMovedConclusion
      ((starRepresentation K (S.fourComponentPointCore z)).comp
        (offenderSubgroup (starRepresentation K (S.fourComponentPointCore z))).subtype)
      ((starImage K (S.fourComponentPointCore z) K).subgroupOf
        (offenderSubgroup (starRepresentation K (S.fourComponentPointCore z)))))
    (a : ActionEquiv (c.source.sectionData.action.comp
      ((starImage K (S.fourComponentPointCore z) K).subgroupOf
        (offenderSubgroup (starRepresentation K (S.fourComponentPointCore z)))).subtype)
      (alternatingNatural 8))
    (hV : V ≤ (⁅starV K (S.fourComponentPointCore z),
      K.subgroupOf (K ⊔ S.fourComponentPointCore z)⁆).map
        (K ⊔ S.fourComponentPointCore z).subtype)
    (hzK : z ∈ centralizer (K : Set G)) : False := by
  let Q := S.fourComponentPointCore z
  let W := (⁅starV K Q,K.subgroupOf (K ⊔ Q)⁆).map (K ⊔ Q).subtype
  have hKW : K ≤ normalizer (W : Set G) := by
    dsimp only [W,Q]
    rw [S.four_overcomponent_star_moved_eq_at structural e hd hz hz1 hzT hK hDK]
    apply ChapterA.Section04.normalizes_signalizerModule K K _ K.le_normalizer
    exact (le_sup_left.trans (K ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ (T : Subgroup G)) (pCore 2 _))
  obtain ⟨π,E,hπ,ha⟩ := ChapterC.C27Source.star_moved_augmentation_ambient
    K Q hCJ c a hz1 ⟨hV hz,hzK⟩
  exact S.four_augmentation_false_at structural e hd hz hz1 hzT K W hK hDK hV hKW hzK π hπ E ha

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

