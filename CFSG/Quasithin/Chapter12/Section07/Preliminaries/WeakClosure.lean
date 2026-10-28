module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The weak-closure deductions in 12.7.11

E.3.10 puts a noncentralizing conjugate inside the actual A₂-family.
The module geometry gives its commutator V₂ and centralizer corank two.
The bound r > 2 then supplies normalization in the reverse direction, so
that conjugate contains t. Uniqueness through t is the contradiction.

Consequently the literal W₀(T,V) centralizes V and w is positive. Its
normalizer is controlled directly by weak closure and the earlier unique
overgroup of N_G(Q). The latter argument uses simplicity only to show that
the normalizer of a nontrivial proper two-subgroup is proper.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.7.11, printed p.843, and E.3.10, E.3.34(2).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07.Preliminaries
open ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The commutator argument of 12.7.11. The module input says that an
A₂-actor has rank two and commutator V₂; it contains no ambient conjugacy
or weak-closure conclusion. The rank bounds are supplied by 12.7.10(2). -/
theorem conjugates_in_T_centralize (V T V₂ : Subgroup G)
    [IsElementaryAbelian 2 V] (t : G) (ht : t ∈ V₂)
    (hTN : T ≤ normalizer (V : Set G))
    (hr : (2 : ℕ∞) < globalR V) (hs : globalS V = 2)
    (hgeometry : ∀ A : Subgroup G, A ≤ T →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
        subgroupCorank A (A ⊓ centralizer (V : Set G)) = 2 ∧ ⁅V, A⁆ = V₂)
    (hunique : ∀ g : G, t ∈ V.conjBy g → V.conjBy g = V)
    (g : G) (hg : V.conjBy g ≤ T) : V.conjBy g ≤ centralizer (V : Set G) := by
  by_contra hn
  have hcomm : ⁅V, V.conjBy g⁆ ≠ ⊥ := by
    intro h
    exact hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h))
  have hAN : V.conjBy g ≤ normalizer (V : Set G) := hg.trans hTN
  have hcorank : subgroupCorank (V.conjBy g)
      (V.conjBy g ⊓ normalizer (V : Set G)) = 0 := by
    rw [inf_eq_left.mpr hAN]
    simp [subgroupCorank]
  have hb : (subgroupCorank (V.conjBy g)
      (V.conjBy g ⊓ normalizer (V : Set G)) : ℕ∞) < globalS V := by
    rw [hcorank, hs]
    decide
  have hfamily := (lemma_E_3_10 V g hb hcomm).2.1
  change inducedAutomizer V (V.conjBy g ⊓ normalizer (V : Set G)) ∈
    fixedSpaceFamily (automizerRepresentation V)
      ((globalS V).toNat - subgroupCorank (V.conjBy g) (V.conjBy g ⊓ normalizer (V : Set G))) at hfamily
  have hf : inducedAutomizer V (V.conjBy g) ∈
      fixedSpaceFamily (automizerRepresentation V) 2 := by
    rw [hcorank, hs] at hfamily
    simpa only [inf_eq_left.mpr hAN, ENat.toNat_ofNat, Nat.sub_zero] using hfamily
  obtain ⟨hcr, hV₂⟩ := hgeometry _ hg hf
  have hrev : V ≤ normalizer (V.conjBy g : Set G) := by
    apply (le_centralizer_iff.mp (show V.conjBy g ⊓ centralizer (V : Set G) ≤
      centralizer (V : Set G) from inf_le_right)).trans
    apply centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
    rw [hcr]
    change (2 : ℕ∞) < globalR (V.map (MulAut.conj g).toMonoidHom)
    rw [globalR_map_equiv]
    exact hr
  have hcommA : ⁅V, V.conjBy g⁆ ≤ V.conjBy g :=
    le_normalizer_iff_commutator_le_right.mp hrev
  have he := hunique g (hcommA (hV₂.symm ▸ ht))
  exact hcomm (by rw [he]; exact commutator_self_eq_bot_iff.mpr inferInstance)

/-- The literal W₀(T,V) centralizes V, and its escape parameter is positive. -/
theorem weakClosure_zero_centralizes (V T V₂ : Subgroup G)
    [IsElementaryAbelian 2 V] (t : G) (ht : t ∈ V₂)
    (hTN : T ≤ normalizer (V : Set G))
    (hr : (2 : ℕ∞) < globalR V) (hs : globalS V = 2)
    (hgeometry : ∀ A : Subgroup G, A ≤ T →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
        subgroupCorank A (A ⊓ centralizer (V : Set G)) = 2 ∧ ⁅V, A⁆ = V₂)
    (hunique : ∀ g : G, t ∈ V.conjBy g → V.conjBy g = V) :
    indexedWeakClosure V T 0 ≤ T ⊓ centralizer (V : Set G) ∧
      0 < globalW V T := by
  have hall := conjugates_in_T_centralize V T V₂ t ht hTN hr hs hgeometry hunique
  constructor
  · apply le_inf (indexedWeakClosure_le V T 0)
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V T A).mp hA
    exact hall g hg
  · apply bot_lt_iff_ne_bot.mpr
    intro he
    obtain ⟨g, hg, hn⟩ := (globalW_eq_zero_iff V T).mp he
    exact hn (hall g hg)

/-- The E.3.34(2) normalizer deduction at i=0, proved directly from weak
closure and the earlier unique-overgroup property of N_G(Q). -/
theorem weakClosure_zero_normalizer_le [IsSimpleGroup G]
    (V Q M : Subgroup G) (T : Sylow 2 G)
    (hV : V ≠ ⊥) (hVT : V ≤ (T : Subgroup G))
    (hWQ : indexedWeakClosure V (T : Subgroup G) 0 ≤ Q)
    (hQT : Q ≤ (T : Subgroup G)) (hnot : ¬ IsPGroup 2 G)
    (hmax : ∀ H : Subgroup G, H ≠ ⊤ → normalizer (Q : Set G) ≤ H → H ≤ M) :
    normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ M := by
  let W := indexedWeakClosure V (T : Subgroup G) 0
  have hVW : V ≤ W := self_le_weakClosure_zero hVT
  have hWp : IsPGroup 2 W := T.isPGroup'.to_le (hWQ.trans hQT)
  have hproper : normalizer (W : Set G) ≠ ⊤ := by
    intro he
    have hn : W.Normal := (normalizer_eq_top_iff.mp he)
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact hV (bot_unique (hb ▸ hVW))
    · apply hnot
      rw [ht] at hWp
      exact hWp.of_equiv Subgroup.topEquiv
  apply hmax _ hproper
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply weakClosure_weakly_closed V (T : Subgroup G) 0 g
  have hQ := mem_normalizer_iff_map_conj_eq.mp hg
  exact ((map_mono hWQ).trans_eq hQ).trans hQT
end CFSG.Quasithin.Chapter12.Section07.Preliminaries
