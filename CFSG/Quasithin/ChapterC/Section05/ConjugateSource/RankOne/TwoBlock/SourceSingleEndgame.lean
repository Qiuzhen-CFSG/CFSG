module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceSingleBlock
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FrattiniEndgame
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Thompson

/-!
# The terminal single-block equalities on the source Sylow group

The actual two-member maximum family and the two full centralizer products
feed the common Frattini argument. Thus the original R-centralizers agree
with their Baumann intersections, and the two-core is the original module.

Import this consumer from the main C.5 umbrella, as its Frattini producer
imports the earlier RankOne umbrella. Source: C.5.6(7)(i), pp.159–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.source_single_block_terminal_equalities
    (h : Setup R K F) (hR : IsPGroup 2 R)
    (H M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G)) (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) → M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    K.pCoreIn 2 = U K ∧
      R ⊓ centralizer (U K : Set G) = S R ⊓ centralizer (U K : Set G) ∧
      R ⊓ centralizer (K : Set G) = S R ⊓ centralizer (K : Set G) := by
  have hp := h.source_single_block_terminal hR H M T_H hRTH hTHM hMR hTHK hH hno x hx hindex hnc
  have hphi := h.frattini_eq_bot_of_index_two H M T_H hTHM hMR hTHK hH hno hindex x hx hnc
  have hq : S R ⊓ centralizer (U K : Set G) ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
    rw [← h.core, h.sylow_maximum_family (hMR hx) hnc hphi]
    exact Set.mem_insert _ _
  have hxout : x ∉ T_H := by
    intro hxt
    have hxU : x ∈ normalizer (U K : Set G) :=
      normalizer_le_normalizer_characteristic_image K (blockU K) (hTHK hxt)
    have he : (U K).map (MulAut.conj x⁻¹).toMonoidHom = U K :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (U K : Set G)).inv_mem hxU)
    apply hnc
    rw [he]
    let := h.elementary
    exact le_centralizer (U K)
  exact ⟨hp.1, centralizer_eq_of_mutual_products R (S R) K (U K)
    hR inf_le_left (map_subtype_le _) h.elementary H M T_H hTHM hMR hTHK hH hno
    x hx hindex hxout hp.2.1 hp.2.2.2 hq⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
