module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Thompson
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.SingleBlockFrattini

/-!
# The rank-one/A₃ conclusion of C.5.7 from the source obstruction

The genuine C.5.2 no-common-normal hypothesis and the coatom block normalizer
kill Φ(D). The natural pair calculation then identifies that normalizer as
the core stabilizer, of index two. Every element outside it exchanges the
two actual cores, which form the full maximum elementary family of S and R.

Source: Aschbacher–Smith C.5.7, printed p.160.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- The complete rank-one family, index and span conclusions of C.5.7,
with Φ(D)=1 discharged by the original common-normal obstruction. -/
theorem Setup.source_C57 (h : Setup R L F) (H M T_H : Subgroup G)
    (hTHM : T_H ≤ M) (hMR : M ≤ normalizer (R : Set G))
    (hTHL : T_H ≤ normalizer (L : Set G)) (hH : H = L ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (hmax : IsCoatom ((normalizer (L : Set G)).subgroupOf M))
    (x : G) (hx : x ∈ M)
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    Phi R L = ⊥ ∧ (normalizer (L : Set G)).relIndex M = 2 ∧
    S R = elementaryAbelianMaxJ R ∧
    ∀ y ∈ M, y ∉ normalizer (L : Set G) →
      S R = Q R L ⊔ (Q R L).map (MulAut.conj y⁻¹).toMonoidHom ∧
      elementaryAbelianMaxSubgroups (S R) =
        {Q R L, (Q R L).map (MulAut.conj y⁻¹).toMonoidHom} ∧
      elementaryAbelianMaxSubgroups R =
        {Q R L, (Q R L).map (MulAut.conj y⁻¹).toMonoidHom} := by
  have hphi : Phi R L = ⊥ :=
    centralizerFrattini_eq_bot_of_coatom R L h.elementary H M T_H hTHM hMR hTHL hH hno hmax
      x hx hnc (h.frattini_invariant (hMR hx) hnc)
  have hi := h.block_normalizer_index M hMR hmax hx hnc hphi
  refine ⟨hphi, hi.2, h.baumann_eq_thompson (hMR hx) hnc hphi, ?_⟩
  intro y hy hyn
  have he : (Q R L).map (MulAut.conj y⁻¹).toMonoidHom ≠ Q R L := by
    intro he
    have hynQ := mem_normalizer_iff_map_conj_eq.mpr he
    have hy' : y⁻¹ ∈ M ⊓ normalizer (Q R L : Set G) := ⟨M.inv_mem hy, hynQ⟩
    have hyL : y⁻¹ ∈ normalizer (L : Set G) := (hi.1.symm ▸ hy').2
    exact hyn (by simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem hyL)
  have hs := (h.core_pair_preserved (hMR hx) hnc hphi (hMR (M.inv_mem hy))).resolve_left he
  rw [hs]
  exact ⟨h.core_span (hMR hx) hnc, h.maximum_family (hMR hx) hnc hphi,
    h.sylow_maximum_family (hMR hx) hnc hphi⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
