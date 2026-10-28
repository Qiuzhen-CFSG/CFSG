module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.NormalizerOrbit

/-!
# Full module fixers preserve the selected source block

The original pair action sends K to K or L. A fixer of U(K) cannot
interchange the blocks, since their original modules are distinct in the
proved four-module orbit. This supplies the normalizer premise in averaging.

Source: Aschbacher–Smith, C.5.6(7), printed pp.158–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G} {F : Type*} [Field F]

theorem Setup.two_block_fixer_normalizes
    (h : Setup R K F) (hKL : L ≤ centralizer (K : Set G)) (hLS : U L ≤ S R)
    (M T_H : Subgroup G) (hRTH : R ≤ T_H)
    (x : G) (hx : x ∈ M) (hxR : x ∈ normalizer (R : Set G))
    (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    R ⊓ centralizer (U K : Set G) ≤ normalizer (K : Set G) := by
  have hi := h.fourModuleSourceInputs hKL hLS M T_H x hx hxR hindex hpair ht hnc
  have hne : U K ≠ U L := by
    intro he
    have hc := commutator_eq_bot_iff_le_centralizer.mp hi.cross_commuting
    rw [← he] at hc
    exact hnc hc
  rintro r ⟨hr,hc⟩
  have hUr : (U K).conjBy r = U K :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hc)
  rcases hpair r (hRTH hr) with he | he
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · have hh := U_map_equiv K (MulAut.conj r)
    change (U K).conjBy r = U (K.conjBy r) at hh
    rw [he,hUr] at hh
    exact (hne hh).elim
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
