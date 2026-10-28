module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import Theory.GroupTheory.PGroup.OmegaCenterDetection
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Triviality of C_T(L) in the t-centralizer branch

A nontrivial C_T(L), normal in the actual Sylow two-subgroup, meets its
first omega center. The earlier implications 12.2.9(1) and 12.4.1 then
produce a noncommuting conjugate of V in T. The established containment
W₀(T,V) ≤ C_T(V) rules it out. Normality remains relative to T throughout.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.7.12, printed p.843 (PDF p.860).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section07.Preliminaries
open ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The elementary two-group step in 12.7.12: a nontrivial C_T(L)
meets the actual Ω₁(Z(T)). No ambient normality of L is assumed. -/
theorem omega_center_centralizer_ne_bot (T : Sylow 2 G) (L : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥) :
    omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro hbot
  apply hne
  apply eq_bot_of_normalized_of_omega_center_disjoint
    (T : Subgroup G) _ T.isPGroup' inf_le_left
  · exact (le_inf (T : Subgroup G).le_normalizer
      (hTL.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  · rw [← omegaCenterIn_eq_omegaOneAmbient]
    apply bot_unique
    exact (inf_le_inf_left _ inf_le_right).trans hbot.le

/-- Source 12.7.12 from 12.2.9(1), the conjugate witness after Sylow
positioning, and the established weak-closure containment of 12.7.11.
The source-facing wrapper below performs the positioning itself. -/
theorem sylow_centralizer_eq_bot (T : Sylow 2 G) (L V M : Subgroup G)
    [IsElementaryAbelian 2 V]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : (1 : ℕ∞) < globalS V)
    (h129 : omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ →
      centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ M)
    (h124 : centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ M →
      (1 : ℕ∞) < globalS V →
        ∃ g : G, V.conjBy g ≤ (T : Subgroup G) ∧ ⁅V, V.conjBy g⁆ ≠ ⊥)
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  by_contra hn
  obtain ⟨g, hg, hcomm⟩ := h124 (h129 (omega_center_centralizer_ne_bot T L hTL hn)) hs
  apply hcomm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  exact (gamma_le_weakClosure ((mem_gamma_zero_iff V (T : Subgroup G) _).mpr
    ⟨g, rfl, hg⟩)).trans (hW.trans inf_le_right)

/-- Put the commutator witness of 12.4.1 in the chosen Sylow subgroup,
using a conjugator in N_G(V) so that V itself is unchanged. -/
theorem position_noncommuting_conjugate (T : Sylow 2 G) (V : Subgroup G)
    (hV : IsPGroup 2 V) (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (g : G) (hne : ⁅V, V.conjBy g⁆ ≠ ⊥) (hle : ⁅V, V.conjBy g⁆ ≤ V) :
    ∃ a : G, V.conjBy a ≤ (T : Subgroup G) ∧ ⁅V, V.conjBy a⁆ ≠ ⊥ := by
  obtain ⟨n, hn, hA⟩ := IsPGroup.exists_conj_le_sylow_of_normalized T
    (normalizer (V : Set G)) (V.conjBy g)
    (hTN.trans (normalizer (V : Set G)).le_normalizer)
    (hV.map (MulAut.conj g).toMonoidHom)
    (le_normalizer_iff_commutator_le_left.mpr hle)
  have hVn : V.map (MulAut.conj n).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hAn : (V.conjBy g).map (MulAut.conj n).toMonoidHom = V.conjBy (n * g) :=
    (conjBy_mul V n g).symm
  refine ⟨n * g, hAn ▸ hA, ?_⟩
  intro hbot
  apply hne
  apply ((⁅V, V.conjBy g⁆).map_eq_bot_iff_of_injective
    (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective).mp
  rw [map_commutator, hVn, hAn]
  exact hbot

/-- Source 12.7.12 with the literal commutator conclusion of 12.4.1.
Sylow positioning is proved above, rather than being added to that input. -/
theorem sylow_centralizer_eq_bot_of_source_witness (T : Sylow 2 G)
    (L V M : Subgroup G) [IsElementaryAbelian 2 V]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hs : (1 : ℕ∞) < globalS V)
    (h129 : omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ →
      centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ M)
    (h124 : centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ M →
      (1 : ℕ∞) < globalS V →
        ∃ g : G, ⁅V, V.conjBy g⁆ ≠ ⊥ ∧ ⁅V, V.conjBy g⁆ ≤ V ⊓ V.conjBy g)
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  apply sylow_centralizer_eq_bot T L V M hTL hs h129 ?_ hW
  intro hc hs
  obtain ⟨g, hne, hle⟩ := h124 hc hs
  exact position_noncommuting_conjugate T V (IsElementaryAbelian.isPGroup 2 V)
    hTN g hne (hle.trans inf_le_left)

end CFSG.Quasithin.Chapter12.Section07.Preliminaries
