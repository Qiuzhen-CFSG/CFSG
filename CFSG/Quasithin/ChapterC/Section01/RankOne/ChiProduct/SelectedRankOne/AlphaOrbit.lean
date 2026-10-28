module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.NormalClosureSupplement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass
/-!
# The literal omega-center span in a Baumann-selected subgroup

The omega center of Baum(T) is the Thompson alpha subgroup. When the
Baumann alpha decomposition is available and G=LT, its normal closure is
[U,L] times the alpha subgroup centralized by L. The latter is also
centralized by Baum(T). Passing to the normal subgroup L Baum(T) therefore
identifies the actual C.1.17 module, without replacing its defining embedding.

Source: Aschbacher–Smith C.1.26, printed p.132, using B.6.10 and C.1.17.
-/
public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem baumann_omega_eq_alpha (T : Subgroup G) :
    omegaOneCenterAmbient (baumann T) = thompsonAlpha T := by
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hA => hA.1
  have hEJ : thompsonAlpha T ≤ elementaryAbelianMaxJ T := by
    intro x hx
    exact ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1
  have hJE : elementaryAbelianMaxJ T ≤ centralizer (thompsonAlpha T : Set G) := by
    intro j hj e he
    exact (((mem_omegaOneCenterAmbient_iff _ e).mp he).2.2 j hj).symm
  have hJB : elementaryAbelianMaxJ T ≤ baumann T := le_inf hJT hJE
  apply le_antisymm
  · let : IsElementaryAbelian 2 (omegaOneCenterAmbient (baumann T)) :=
      omegaOneCenterAmbient_elementaryAbelian _
    apply elementary_centralizer_maxJ_le_omegaCenter T _
    · intro x hx
      exact ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1.1
    · intro x hx j hj
      exact ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2 j (hJB hj)
  · intro e he
    have heE := (mem_omegaOneCenterAmbient_iff _ e).mp he
    exact (mem_omegaOneCenterAmbient_iff _ e).mpr
      ⟨hJB (hEJ he), heE.2.1, fun b hb => (hb.2 e he).symm⟩

omit [Finite G] in
theorem alpha_normalized (T : Subgroup G) :
    T ≤ normalizer (thompsonAlpha T : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (omegaOneCenterAmbient (elementaryAbelianMaxJ T)).map
    (MulAut.conj t).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective,
    ← elementaryAbelianMaxJ_map_equiv,
    ]
  have hh : T.map (MulAut.conj t).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer ht)
  rw [hh]
  rfl

theorem alpha_normalClosure_eq_moved_sup_fixed (T U L : Subgroup G)
    [U.Normal] [L.Normal] (hgen : L ⊔ T = ⊤)
    (hU : U = normalClosure (omegaOneCenterAmbient T : Set G))
    (ha : thompsonAlpha T ≤ ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    normalClosure (thompsonAlpha T : Set G) =
      ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)) := by
  let D := thompsonAlpha T ⊓ centralizer (L : Set G)
  have hLD : L ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp (show D ≤ centralizer (L:Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTD : T ≤ normalizer (D : Set G) := by
    have hTC : T ≤ normalizer (centralizer (L:Set G) : Set G) := le_normalizer_of_normal
    exact (le_inf (alpha_normalized T) hTC).trans inf_normalizer_le_normalizer_inf
  let : D.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hLD hTD))
  have hUe : U ≤ normalClosure (thompsonAlpha T : Set G) := by
    rw [hU]
    exact normalClosure_mono (omegaCenter_le_omegaCenter_maxJ T)
  apply le_antisymm (normalClosure_le_normal ha)
  exact sup_le ((commutator_le_left _ _).trans hUe) (inf_le_left.trans le_normalClosure)


omit [Finite G] in
theorem baumann_residual_join_normal (T L : Subgroup G) [L.Normal]
    (hgen : L ⊔ T = ⊤) : (L ⊔ baumann T).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  refine sup_le ((show L ≤ L ⊔ baumann T from le_sup_left).trans (L ⊔ baumann T).le_normalizer) ?_
  have hb : T ≤ normalizer (baumann T : Set G) :=
    T.le_normalizer.trans (normalizer_le_normalizer_baumann T)
  exact (le_inf (le_normalizer_of_normal : T ≤ normalizer (L:Set G)) hb).trans
    (normalizer_inf_normalizer_le_normalizer_sup L (baumann T))

theorem localV_selected_baumann_map (T L : Subgroup G) [L.Normal]
    (hgen : L ⊔ T = ⊤) :
    (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype = normalClosure (thompsonAlpha T : Set G) := by
  let N := L ⊔ baumann T
  let : N.Normal := baumann_residual_join_normal T L hgen
  have hEN : thompsonAlpha T ≤ N := by
    rw [←baumann_omega_eq_alpha T]
    intro x hx
    exact (show baumann T ≤ N from le_sup_right)
      (((mem_omegaOneCenterAmbient_iff _ x).mp hx).1)
  have hNT : N ⊔ T = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le_sup le_sup_left le_rfl
  have he : (GlaubermanNiles.omegaCenter (baumann T)).map
      (inclusion (show baumann T ≤ N from le_sup_right)) = (thompsonAlpha T).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hEN]
    change omegaOneCenterAmbient (baumann T) = thompsonAlpha T
    exact baumann_omega_eq_alpha T
  change (normalClosure (_ : Set N)).map N.subtype = _
  rw [he]
  exact (normalClosure_eq_map_of_normal_supplement N T (thompsonAlpha T)
    hNT hEN (alpha_normalized T)).symm

theorem localV_selected_baumann_eq_moved_sup_fixed (T U L : Subgroup G)
    [U.Normal] [L.Normal] (hgen : L ⊔ T = ⊤)
    (hU : U = normalClosure (omegaOneCenterAmbient T : Set G))
    (ha : thompsonAlpha T ≤ ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype =
      ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G)) := by
  rw [localV_selected_baumann_map T L hgen]
  exact alpha_normalClosure_eq_moved_sup_fixed T U L hgen hU ha
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
