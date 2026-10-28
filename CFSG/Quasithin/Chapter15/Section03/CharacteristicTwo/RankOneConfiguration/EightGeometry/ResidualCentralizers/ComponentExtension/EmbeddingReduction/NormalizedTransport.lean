module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.Transport

/-!
# Retaining full Sylow normalization in the component quotient

Intersect the original Sylow subgroup with the subnormal containing
component, then project modulo its two-core. The same quotient Sylow both
witnesses the local C-component and normalizes its actual embedded image.
This additional conclusion is used by the normalized J₄ and L₅(2) model
exclusions in the original fixed-line argument.

Source: Aschbacher–Smith15.3.32(3), printed p.1133.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
open Chapter1 Chapter1.Section02 Chapter1.Terminal Chapter1.Terminal.LinearFourActions
variable {G : Type*} [Group G] [Finite G]

/-- The projected local section is normalized by the same full quotient Sylow. -/
theorem exists_image_normalized_local_sylow (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hBK : B ≤ K) (hK : K.IsCComponent) :
    ∃ T : Sylow 2 (XiQuotient K),
      twoQuotientImage B K ∈ ChapterA.Section03.localCComponents T ∧
      T.toSubgroup ≤ normalizer (twoQuotientImage B K : Set (XiQuotient K)) := by
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  let q := QuotientGroup.mk' (pCore 2 K)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := K)
    infer_instance
  refine ⟨R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · change (B.subgroupOf K).map q ∈ ChapterA.Section03.localCComponents ((R : Subgroup K).map q)
    rw [hR]
    exact localCComponents_map_of_solvable_ker (local_subgroupOf hB hSB hBK) q
  · change (R : Subgroup K).map q ≤ normalizer ((B.subgroupOf K).map q : Set (XiQuotient K))
    apply (map_mono ?_).trans (le_normalizer_map q)
    rw [hR, ← subgroupOf_normalizer_eq hBK]
    exact comap_mono hSB

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
