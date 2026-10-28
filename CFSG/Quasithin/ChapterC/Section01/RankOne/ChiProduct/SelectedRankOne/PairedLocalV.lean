module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.AlphaOrbit
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
/-!
# The literal local module for an individual Baumann-normalized factor

The omega center of the original Baumann subgroup is the Thompson alpha
subgroup. Since Baumann centralizes alpha and normalizes the given factor,
its addition does not enlarge the factor orbit span. This identifies the
actual C.1.17 module for the factor inclusion, without changing the Sylow
subgroup or assuming that the factor is normal in the ambient group.

Source: Aschbacher–Smith C.1.26 and B.6.10, pp.132 and 117.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

theorem localV_factor_baumann_map (T K : Subgroup G)
    (hBK : baumann T ≤ normalizer (K : Set G)) :
    (localV (inclusion (show baumann T ≤ K ⊔ baumann T from le_sup_right))).map
      (K ⊔ baumann T).subtype = conjugateSpanBy (thompsonAlpha T) K := by
  let B := baumann T
  let N := K ⊔ B
  let E := thompsonAlpha T
  have hEB : E ≤ B := by
    rw [show E = thompsonAlpha T from rfl,←baumann_omega_eq_alpha T]
    intro x hx
    exact ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1
  have hEN : E ≤ N := hEB.trans le_sup_right
  have he : (omegaCenter B).map (inclusion (show B ≤ N from le_sup_right)) = E.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hEN]
    change omegaOneCenterAmbient (baumann T) = thompsonAlpha T
    exact baumann_omega_eq_alpha T
  have hBE : B ≤ normalizer (E : Set G) :=
    (show B ≤ centralizer (E : Set G) from inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hBC : B ≤ normalizer (conjugateSpanBy E K : Set G) := by
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp (hBE hb),
      mem_normalizer_iff_map_conj_eq.mp (hBK hb)]
  have hspan : conjugateSpanBy E N = conjugateSpanBy E K :=
    le_antisymm (conjugateSpanBy_le (le_conjugateSpanBy E K)
      (sup_le (le_normalizer_conjugateSpanBy E K) hBC))
      (conjugateSpanBy_mono le_rfl le_sup_left)
  change (normalClosure (_ : Set N)).map N.subtype = _
  rw [he,normalClosure_subgroupOf_eq_conjugateSpanBy E N hEN,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hEN),hspan]
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
