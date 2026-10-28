module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamilyAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.SingleBlockFrattini
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# The A₅ source normalizer theorem C.5.7

The genuine common-normal-subgroup obstruction eliminates Φ(D) when the
block normalizer is maximal. The proved action on the R-invariant core pair
then makes that normalizer the core stabilizer, of index two. Every element
outside it gives the source core span and the four-member elementary family,
with the actual inner conjugator r and its index-two intersection.

Source: Aschbacher–Smith, C.5.7, printed p.160, using C.5.1–5.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

omit [Finite G] in
private theorem block_normalizer_core_normalizer (_h : AlternatingPairSetup R K L)
    (M : Subgroup G) (hMR : M ≤ normalizer (R : Set G)) :
    M ⊓ normalizer (K : Set G) ≤ normalizer ((K ⊔ ChapterB.baumann R).pCoreIn 2 : Set G) := by
  have hS := hMR.trans (normalizer_le_normalizer_baumann R)
  exact ((le_inf inf_le_right (inf_le_left.trans hS)).trans
    (normalizer_inf_normalizer_le_normalizer_sup K (ChapterB.baumann R))).trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ ChapterB.baumann R)
      (pCore 2 (K ⊔ ChapterB.baumann R : Subgroup G)))

theorem AlternatingPairSetup.block_normalizer_index
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (M : Subgroup G) (hMR : M ≤ normalizer (R : Set G))
    (hmax : IsCoatom ((normalizer (K : Set G)).subgroupOf M))
    (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let Q := (K ⊔ ChapterB.baumann R).pCoreIn 2
    M ⊓ normalizer (K : Set G) = M ⊓ normalizer (Q : Set G) ∧
      (normalizer (K : Set G)).relIndex M = 2 := by
  let Q := (K ⊔ ChapterB.baumann R).pCoreIn 2
  have he := coatom_eq_pair_normalizer M (M ⊓ normalizer (K : Set G)) Q
    (Q.map (MulAut.conj x⁻¹).toMonoidHom) inf_le_left
    (by
      have he : (M ⊓ normalizer (K : Set G)).subgroupOf M =
          (normalizer (K : Set G)).subgroupOf M := by
        ext m
        exact and_iff_right m.property
      exact he.symm ▸ hmax)
    (block_normalizer_core_normalizer h M hMR)
    (fun m hm => h.core_pair_preserved hRK x (hMR hx) hnc hphi m (hMR hm))
    x⁻¹ (M.inv_mem hx) (by
      intro he
      have hUQ : sourceModule K ≤ Q := le_sup_left.trans_eq h.product.symm
      exact hnc (((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hUQ).trans_eq he).trans
        (h.core.le.trans inf_le_right)))
  exact ⟨he.1, by simpa only [inf_relIndex_left] using he.2⟩

/-- All A₅ family, normalizer, index and span conclusions of the single-block C.5.7 source. -/
theorem AlternatingPairSetup.source_C57
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M) (hMR : M ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G)) (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (hmax : IsCoatom ((normalizer (K : Set G)).subgroupOf M))
    (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    (frattini D).map D.subtype = ⊥ ∧ (normalizer (K : Set G)).relIndex M = 2 ∧
    S = elementaryAbelianMaxJ R ∧
    ∀ y ∈ M, y ∉ normalizer (K : Set G) →
      S = Q ⊔ Q.map (MulAut.conj y⁻¹).toMonoidHom ∧
      ∃ A : Subgroup G, ∃ r : G,
        r ∈ R ⊓ K ∧ r ∉ S ∧ Q.relIndex A = 2 ∧
        elementaryAbelianMaxSubgroups R =
          {Q, Q.map (MulAut.conj y⁻¹).toMonoidHom, A, A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  have hU : IsElementaryAbelian 2 (sourceModule K) := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  have hphi := centralizerFrattini_eq_bot_of_coatom R K hU H M T_H hTHM hMR hTHK hH hno hmax
    x hx hnc (h.frattini_invariant x (hMR hx) hnc)
  have hi := h.block_normalizer_index hRK M hMR hmax x hx hnc hphi
  refine ⟨hphi, hi.2, h.baumann_eq_maxJ x (hMR hx) hnc hphi, ?_⟩
  intro y hy hyn
  have hmove : ((K ⊔ ChapterB.baumann R).pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom ≠
      (K ⊔ ChapterB.baumann R).pCoreIn 2 := by
    intro he
    have hynQ := mem_normalizer_iff_map_conj_eq.mpr he
    have hy' : y⁻¹ ∈ M ⊓ normalizer ((K ⊔ ChapterB.baumann R).pCoreIn 2 : Set G) :=
      ⟨M.inv_mem hy, hynQ⟩
    have hyK : y⁻¹ ∈ normalizer (K : Set G) := (hi.1.symm ▸ hy').2
    exact hyn (by simpa only [inv_inv] using (normalizer (K : Set G)).inv_mem hyK)
  have hs := (h.core_pair_preserved hRK x (hMR hx) hnc hphi y⁻¹ (hMR (M.inv_mem hy))).resolve_left hmove
  rw [hs]
  exact ⟨h.core_conjugate_span x (hMR hx) hnc, h.single_block_family hRK x (hMR hx) hnc hphi⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
