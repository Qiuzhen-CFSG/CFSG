module

public import CFSG.Quasithin.ChapterE.Section01.MinimalParabolicGeneration
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.SolvableSource

/-!
# The actual 13.6.25 consumer of minimal-parabolic generation

The source quantifies over all H(T,M), without a minimality restriction.
Positive E-generation witnesses for the actual intrinsic minimal parabolics
of each such H give an attained parameter of H by E.1.12 and B.6.6. The
proved E.3.35 containment then forces n(H)>1. Its solvable clause supplies
the remaining containment conclusion independently.

The earlier A5 setup and the local minimal-parabolic witnesses remain
explicit. The normal and exchanged-component E.2 source producers own their
discharge; this theorem does not assert unrestricted E.1.11 existence.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.6.25, printed pp.933--934; E.1.12, printed p.214.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open Subgroup Theory.GroupTheory
open _root_.CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]
namespace EarlierA5Setup
variable {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV)
include s

theorem generationParameter_gt_one_of_minimalParabolics (ha : localA V = 1)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hlocal : ∀ P : Subgroup H,
      ChapterB.IsMinimalParabolicOver (T.subtype hH.1.2) P →
      ∃ n : ℕ, 0 < n ∧ IsEGenerated n P) : 1 < generationParameter H := by
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    apply hH.1.1
    change (pCore 2 H).map H.subtype = ⊥
    rw [he, Subgroup.map_bot]
  let : Nontrivial (pCore 2 H) := (nontrivial_iff_ne_bot _).mpr hcore
  obtain ⟨n, hn, hc⟩ := (pCore_isPGroup (p := 2) (G := H)).nontrivial_iff_card.mp
    (inferInstance : Nontrivial (pCore 2 H))
  have heven : ¬ Odd (Nat.card H) := by
    apply Nat.not_odd_iff_even.mpr
    apply even_iff_two_dvd.mpr
    apply dvd_trans _ (card_subgroup_dvd_card (pCore 2 H))
    rw [hc]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  have hpos := (generationParameter_spec heven
    (exists_generation_of_minimalParabolics (T.subtype hH.1.2) hlocal)).1
  by_contra hnot
  have hle : generationParameter H ≤ 1 := by omega
  apply hH.2
  apply SourceContainment.le_of_generationParameter_pos s.hypothesisE322
    (T.subtype hH.1.2) s.unique_over_core_normalizer
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (s.module_normalizer ▸ s.normalizer_le))
  · change (T : Subgroup G) ⊓ centralizer (V : Set G) ≤
      ((T : Subgroup G).subgroupOf H).map H.subtype
    rw [map_subgroupOf_eq_of_le hH.1.2]
    exact inf_le_left
  · exact hpos
  · apply lt_min
    · exact lt_of_le_of_lt (by exact_mod_cast hle) (s.globalW_gt_one ha)
    · rw [s.globalR_eq_three]
      exact lt_of_le_of_lt (show (generationParameter H : ℕ∞) ≤ 1 by exact_mod_cast hle)
        (by norm_num)
end EarlierA5Setup

/-- All original 13.6.25 conclusions, retaining precisely the local generation witnesses. -/
theorem source_13_6_25_of_minimalParabolic_generation
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (ha : localA V = 1)
    (hlocal : ∀ (H : Subgroup G)
      (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)),
      ∀ P : Subgroup H, ChapterB.IsMinimalParabolicOver (T.subtype hH.1.2) P →
        ∃ n : ℕ, 0 < n ∧ IsEGenerated n P) :
    (∀ i : ℕ, i = 0 ∨ i = 1 →
      indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter3.NormalIn (indexedWeakClosure V (T : Subgroup G) i) (L ⊔ (T : Subgroup G))) ∧
    (∀ H ∈ Chapter1.HOutside G (T : Set G) (M : Set G), 1 < generationParameter H) ∧
    (∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H → H ≤ M) ∧
    globalR V = 3 ∧ 1 < globalW V (T : Subgroup G) :=
  ⟨fun _ hi => s.weakClosure_core_and_normal ha hi,
    fun H hH => s.generationParameter_gt_one_of_minimalParabolics ha hH (hlocal H hH),
    s.solvable_HOver_le_source ha, s.globalR_eq_three, s.globalW_gt_one ha⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
