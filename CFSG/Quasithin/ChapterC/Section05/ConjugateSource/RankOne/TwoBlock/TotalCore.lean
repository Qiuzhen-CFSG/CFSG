module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.PairedCores
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoreProduct

/-!
# The source total module is the full two-core of the block product

Gaschütz identifies each original block core using the actual elementary
intersection Q. The multiplication map of the commuting short blocks has
a central two-kernel, so core lifting gives the total equality without
assuming that the blocks or their natural covers split.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
variable {F F' : Type*} [Field F] [Field F']

theorem Setup.two_block_core_eq_module
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (hSylow : ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hSylow' : ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S R ⊓ L)
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M) (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer (K ⊔ L : Subgroup G)) (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) → M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) : (K ⊔ L).pCoreIn 2 = U K ⊔ U L := by
  obtain ⟨hK,hL⟩ := h.two_block_individual_cores h' hR hKL hSylow hSylow' H M T_H hTHM hMR hTHKL hH hno
    x hx hindex hpair ht hnc
  rw [short_commuting_core_product h.short h'.short hKL,hK,hL]
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
