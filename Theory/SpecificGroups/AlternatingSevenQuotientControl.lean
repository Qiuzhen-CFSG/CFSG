module
public import Theory.SpecificGroups.AlternatingSevenNormalControl
public import Theory.GroupTheory.CentralizerQuotientNormalizer
/-!
# Normalizer control from an actual normal A₇ quotient image

The original Sylow image is self-normalizing modulo the centralizer of
the normal A₇ subgroup. Its normalizer therefore preserves the smaller
subgroup image, and thus its commutator with V in the original group.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem normalizer_commutator_le_of_alternatingSeven_image
    (V K : Subgroup G) [V.Normal] (P : Sylow 2 G)
    (hPK : (P : Subgroup G) ≤ normalizer (K : Set G))
    (L : Subgroup (G ⧸ centralizer (V : Set G))) [L.Normal]
    (hKL : K.map (QuotientGroup.mk' (centralizer (V : Set G))) ≤ L)
    (e : L ≃* alternatingGroup (Fin 7)) :
    normalizer (P : Set G) ≤ normalizer (⁅V,K⁆ : Subgroup G) := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V : Set G)))
  have hn := AlternatingSevenNormal.sylow_normalizer_le L e Q
  have ht : (Q : Subgroup (G ⧸ centralizer (V : Set G))) ≤ normalizer (K.map q : Set _) :=
    (map_mono hPK).trans (K.le_normalizer_map q)
  have hc : centralizer (L : Set (G ⧸ centralizer (V : Set G))) ≤
      normalizer (K.map q : Set (G ⧸ centralizer (V : Set G))) :=
    (centralizer_le hKL).trans (centralizer_le_normalizer _)
  have hm : (normalizer (P : Set G)).map q ≤ normalizer (K.map q : Set _) :=
    ((P : Subgroup G).le_normalizer_map q).trans (hn.trans (sup_le ht hc))
  exact (map_le_iff_le_comap.mp hm).trans (normalizer_centralizerQuotient_image_le V K)
end Subgroup
