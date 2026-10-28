module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.SylowAction
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Detecting a short block in a centralizing product

If L is covered by C(V)D with D centralizing L, conjugation by each
l in L on L equals conjugation by an element centralizing V. Thus
[V,L] centralizes L. Since V lies in the centralizer of a Sylow
subgroup of a characteristic-two group, it lies in the two-core and
normalizes L. The group V[V,L] is a two-group normalized by L;
two-perfection and commutator idempotence now give [V,L] = 1.

Consequently exact C.1.9 identifies a block not centralizing V with
one member of any covering block family. This proof uses the actual
short-group definition and works for the nonperfect A₃ alternative.
It needs neither an A₄ marking nor membership in a perfect family.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.7–9, printed p.123, and E.6.23, printed p.254. The core-action
and coprime-idempotence arguments use the proved finite-group lemmas.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection

private theorem centralizes_of_centralizing_product {G : Type*} [Group G] [Finite G]
    (L P V D : Subgroup G) (hp : IsPGroup 2 P) (hLP : L ≤ normalizer P)
    (hVL : V ≤ normalizer L) (hVP : V ≤ P) (hL : IsPPerfect 2 L)
    (hD : D ≤ centralizer (L : Set G))
    (hcover : ∀ l ∈ L, ∃ m ∈ centralizer (V : Set G), ∃ d ∈ D, m * d = l) :
    ⁅V, L⁆ = ⊥ := by
  have hc : ⁅V, L⁆ ≤ centralizer (L : Set G) := by
    apply commutator_le.mpr
    intro v hv l hl
    obtain ⟨m, hm, d, hd, he⟩ := hcover l hl
    have hdN : d ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ (hD hd)
    have hmN : m ∈ normalizer (L : Set G) := by
      rw [← mul_inv_cancel_right m d, he]
      exact (normalizer (L : Set G)).mul_mem (L.le_normalizer hl)
        ((normalizer (L : Set G)).inv_mem hdN)
    let vN : normalizer (L : Set G) := ⟨v, hVL hv⟩
    let lN : normalizer (L : Set G) := ⟨l, L.le_normalizer hl⟩
    let mN : normalizer (L : Set G) := ⟨m, hmN⟩
    let dN : normalizer (L : Set G) := ⟨d, hdN⟩
    let f := L.normalizerMonoidHom
    have hd1 : f dN = 1 := by
      exact (show dN ∈ f.ker by rw [normalizerMonoidHom_ker]; exact hD hd)
    have hlm : f lN = f mN := by
      have heN : mN * dN = lN := Subtype.ext he
      rw [← heN, map_mul, hd1, mul_one]
    have hcomm : Commute (f vN) (f lN) := by
      rw [hlm]
      apply Commute.map
      exact Subtype.ext (mem_centralizer_iff.mp hm v hv)
    have hh : ⁅vN, lN⁆ ∈ f.ker := by
      change f ⁅vN, lN⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  let W := ⁅V, L⁆
  have hWP : W ≤ P := (commutator_mono hVP le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hLP)
  have hWC : ⁅W, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
  have he : ⁅V ⊔ W, L⁆ = W := by
    rw [commutator_comm]
    exact (commutator_eq_of_centralizing_sup (sup_comm W V) hc hVL).symm.trans
      (commutator_comm L V)
  have hn : L ≤ normalizer (V ⊔ W : Subgroup G) :=
    le_normalizer_iff_commutator_le_left.mpr (he.le.trans le_sup_right)
  have hi := commutator_isPPerfect_idempotent L (V ⊔ W) hL
    (hp.to_le (sup_le hVP hWP)) hn
  rw [he, hWC] at hi
  exact hi.symm

/-- A centralizing product cannot hide a nontrivial action on a short block. -/
theorem block_centralizes_of_centralizing_product {G : Type*} [Group G] [Finite G]
    (hG : generalizedFitting G = pCore 2 G) (Q : Sylow 2 G)
    (L V D : Subgroup G) (hL : ChapterC.IsBlock L)
    (hV : V ≤ centralizer (Q : Set G))
    (hD : D ≤ centralizer (L : Set G))
    (hcover : ∀ l ∈ L, ∃ m ∈ centralizer (V : Set G), ∃ d ∈ D, m * d = l) :
    ⁅V, L⁆ = ⊥ :=
  centralizes_of_centralizing_product L (pCore 2 G) V D pCore_isPGroup
    (by rw [normalizer_eq_top]; exact le_top)
    (hV.trans (central_sylow_normalizes_block hG Q L hL))
    (hV.trans (central_sylow_le_core hG Q)) hL.short.twoPerfect hD hcover

/-- Exact block commutation detects an escaping block among a covering family. -/
theorem block_eq_factor_of_centralizing_product {G : Type*} [Group G] [Finite G] {I : Type*}
    (hG : generalizedFitting G = pCore 2 G) (Q : Sylow 2 G)
    (L V : Subgroup G) (hL : ChapterC.IsBlock L)
    (hV : V ≤ centralizer (Q : Set G))
    (B : I → Subgroup G) (hB : ∀ i, ChapterC.IsBlock (B i))
    (hcomm : ∀ X Y : Subgroup G, ChapterC.IsBlock X → ChapterC.IsBlock Y →
      X ≠ Y → ⁅X, Y⁆ = ⊥)
    (hcover : ∀ l ∈ L, ∃ m ∈ centralizer (V : Set G),
      ∃ d ∈ ⨆ i, B i, m * d = l)
    (he : ¬ L ≤ centralizer (V : Set G)) : ∃ i, L = B i := by
  classical
  by_contra! hne
  have hc : (⨆ i, B i) ≤ centralizer (L : Set G) :=
    iSup_le fun i => commutator_eq_bot_iff_le_centralizer.mp
      (hcomm (B i) L (hB i) hL (Ne.symm (hne i)))
  have hz := block_centralizes_of_centralizing_product hG Q L V (⨆ i, B i) hL hV hc hcover
  exact he (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
