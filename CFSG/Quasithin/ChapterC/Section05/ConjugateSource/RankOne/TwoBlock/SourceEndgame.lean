module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceTerminal
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FrattiniEndgame

/-!
# The terminal two-block equalities on the source Sylow group

The marked source action supplies both full centralizer products and the
maximum elementary core. The common Frattini argument puts both original
R-centralizers inside Baum(R), completing the terminal core identification.
All Sylow and natural-cover inputs are derived from the original setups.

Source: Aschbacher–Smith, C.5.6(7)(ii), printed pp.159–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
variable {F F' : Type*} [Field F] [Field F']

theorem Setup.source_two_block_terminal_equalities
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (H M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer (K ⊔ L : Subgroup G)) (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) → M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let U₀ := U K ⊔ U L
    (K ⊔ L).pCoreIn 2 = U₀ ∧
      R ⊓ centralizer (U₀ : Set G) = S R ⊓ centralizer (U₀ : Set G) ∧
      R ⊓ centralizer (K ⊔ L : Subgroup G) = S R ⊓ centralizer (K ⊔ L : Subgroup G) := by
  have hp := h.source_two_block_terminal h' hR hKL H M T_H hRTH hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hq := h.two_block_maximum_core h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hU : IsElementaryAbelian 2 (U K ⊔ U L : Subgroup G) := by
    let := h.elementary
    let := h'.elementary
    exact IsElementaryAbelian.sup_of_le_centralizer
      ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _))))
  exact ⟨hp.1, centralizer_eq_of_mutual_products R (S R) (K ⊔ L) (U K ⊔ U L)
    hR inf_le_left (sup_le_sup (map_subtype_le _) (map_subtype_le _)) hU
    H M T_H hTHM hMR hTHKL hH hno x hx hindex hi.x_outside hp.2.1 hp.2.2.2 hq.1⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
