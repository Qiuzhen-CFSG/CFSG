module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.SourceSylow
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.TotalCore
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.TerminalConjugate
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SingleBlockTerminal

/-!
# The terminal rank-one source identities with the Sylow premises discharged

The original marked quotient constructs the same Sylow intersections used
by both Gaschütz arguments. Applying those producers gives the two-core
and both full centralizer products on the original source subgroups, with
no extra natural-module, central-cover or Sylow input.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
variable {F F' : Type*} [Field F] [Field F']

theorem Setup.source_two_block_terminal
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
    let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
    let C := R ⊓ centralizer (K ⊔ L : Subgroup G)
    (K ⊔ L).pCoreIn 2 = U₀ ∧
      R ⊓ centralizer (U₀ : Set G) = U₀ ⊔ C ∧
      C ≤ centralizer (V : Set G) ∧ R ⊓ centralizer (V : Set G) = V ⊔ C := by
  have hs := h.source_sylow_block hR
  have hs' := h'.source_sylow_block hR
  exact ⟨h.two_block_core_eq_module h' hR hKL hs hs' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc,
    h.two_block_full_centralizer_product h' hR hKL (fun _ => hs) (fun _ => hs') M T_H hRTH hTHM
      x hx (hMR hx) hindex hpair ht hnc,
    h.two_block_full_centralizer_centralizes h' hR hKL (fun _ => hs) (fun _ => hs') M T_H hRTH hTHM
      x hx (hMR hx) hindex hpair ht hnc,
    h.two_block_conjugate_full_centralizer_product h' hR hKL (fun _ => hs) (fun _ => hs') M T_H hRTH hTHM
      x hx (hMR hx) hindex hpair ht hnc⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
