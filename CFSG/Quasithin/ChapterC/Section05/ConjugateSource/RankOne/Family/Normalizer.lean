module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.EvenOrder
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# The actual normalizer pair in the rank-one C.5.7 branch

Every subgroup normalizing R preserves S and its proved maximum elementary
family. The source conjugator moves Q, so the actual relative normalizer
of Q has index two. If N_M(K) is maximal, it equals that stabilizer.
The source common-normal obstruction remains responsible for Φ(D)=1.

Source: Aschbacher–Smith, C.5.7, printed p.160.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- Every original R-normalizer preserves the computed pair of actual cores. -/
theorem Setup.core_pair_preserved (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) {m : G} (hm : m ∈ normalizer (R : Set G)) :
    (Q R L).map (MulAut.conj m).toMonoidHom = Q R L ∨
    (Q R L).map (MulAut.conj m).toMonoidHom = (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
  have hq : Q R L ∈ elementaryAbelianMaxSubgroups (S R) := by
    rw [h.maximum_family hx hnc hphi]
    exact Set.mem_insert _ _
  have hmap := (maxFamily_map_injective_iff (MulAut.conj m).toMonoidHom
    (MulAut.conj m).injective (S R) (Q R L)).mpr hq
  have hmS : (S R).map (MulAut.conj m).toMonoidHom = S R :=
    mem_normalizer_iff_map_conj_eq.mp (Stellmacher.normalizer_le_normalizer_baumann R hm)
  rw [hmS, h.maximum_family hx hnc hphi] at hmap
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmap

/-- The exact core normalizer has index two in the original M. -/
theorem Setup.core_normalizer_index (h : Setup R L F) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) {x : G} (hx : x ∈ M)
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) : (normalizer (Q R L : Set G)).relIndex M = 2 := by
  apply normalizer_relIndex_eq_two_of_pair M (Q R L)
    ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom)
    (fun m hm => h.core_pair_preserved (hMR hx) hnc hphi (hMR hm)) x⁻¹ (M.inv_mem hx)
  intro he
  exact hnc (((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) h.module_le_core).trans_eq he).trans
    (h.core ▸ inf_le_right))

omit [Finite G] in
/-- The original block normalizer preserves the actual two-core of KS. -/
theorem Setup.block_normalizer_le_core_normalizer (_h : Setup R L F) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) :
    M ⊓ normalizer (L : Set G) ≤ normalizer (Q R L : Set G) := by
  have hS := hMR.trans (Stellmacher.normalizer_le_normalizer_baumann R)
  exact ((le_inf inf_le_right (inf_le_left.trans hS)).trans
    (normalizer_inf_normalizer_le_normalizer_sup L (S R))).trans
    (normalizer_le_normalizer_characteristic_image (L ⊔ S R) (pCore 2 (L ⊔ S R : Subgroup G)))

/-- The coatom hypothesis of C.5.7 identifies N_M(K) with the actual
index-two core stabilizer. The family theorem supplies its pair action. -/
theorem Setup.block_normalizer_index (h : Setup R L F) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G))
    (hmax : IsCoatom ((normalizer (L : Set G)).subgroupOf M))
    {x : G} (hx : x ∈ M)
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) :
    M ⊓ normalizer (L : Set G) = M ⊓ normalizer (Q R L : Set G) ∧
      (normalizer (L : Set G)).relIndex M = 2 := by
  have he := coatom_eq_pair_normalizer M (M ⊓ normalizer (L : Set G)) (Q R L)
    ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom) inf_le_left
    (by
      have he : (M ⊓ normalizer (L : Set G)).subgroupOf M =
          (normalizer (L : Set G)).subgroupOf M := by
        ext m
        exact and_iff_right m.property
      exact he.symm ▸ hmax)
    (h.block_normalizer_le_core_normalizer M hMR)
    (fun m hm => h.core_pair_preserved (hMR hx) hnc hphi (hMR hm)) x⁻¹ (M.inv_mem hx)
    (fun he => hnc (((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom)
      h.module_le_core).trans_eq he).trans (h.core ▸ inf_le_right)))
  exact ⟨he.1, by simpa only [inf_relIndex_left] using he.2⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
