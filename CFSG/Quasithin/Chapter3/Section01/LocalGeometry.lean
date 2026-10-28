module

public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.TINormalizerControl
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Local overgroups in the common-normal-subgroup argument

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Definition
3.0.1 and Lemmas 3.1.2–3.1.4, pp. 571–572.

A subgroup containing a Sylow subgroup contains the two-core of each of its
overgroups. This proves interval closure of `H(T)`, so a minimal member
outside `M` has `H ∩ M` as its unique maximal subgroup above `T`.
The TI calculation is the general normalizer-control theorem. The last
lemma excludes common normal two-subgroups using uniqueness of a maximal
two-local overgroup, as required in Theorems 3.1.8 and 3.1.9.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter3

open Subgroup

variable {G : Type*} [Group G]

theorem normalIn_iff_le_normalizer {N K : Subgroup G} :
    NormalIn N K ↔ N ≤ K ∧ K ≤ normalizer (N : Set G) := by
  rw [NormalIn, le_normalizer_iff]

theorem generated_eq_sup (A B : Subgroup G) : generated A B = A ⊔ B := by
  exact le_antisymm
    ((closure_le _).mpr (Set.union_subset
      (show (A : Set G) ⊆ (A ⊔ B : Subgroup G) from (show A ≤ A ⊔ B from le_sup_left))
      (show (B : Set G) ⊆ (A ⊔ B : Subgroup G) from (show B ≤ A ⊔ B from le_sup_right))))
    (sup_le le_generated_left le_generated_right)

/-- The two-core inclusion used in the proof of 3.1.2 (source A.1.6). -/
theorem twoCore_le_of_sylow_le (T : Sylow 2 G) {Y H : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hYH : Y ≤ H) : H.pCoreIn 2 ≤ Y.pCoreIn 2 := by
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype (hTY.trans hYH))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (hTY.trans hYH)] using hh
  have hnorm : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 H).le_normalizer_map H.subtype
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
    (hcoreT.trans hTY) (hYH.trans hnorm)

/-- The interval-closure assertion of 3.1.2. The additional `He` assertion
uses 1.1.4(6), independently of this purely Sylow-theoretic statement. -/
theorem mem_HOver_of_sylow_interval (T : Sylow 2 G) {Y H : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hYH : Y ≤ H)
    (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    Y ∈ Chapter1.HOver G (T : Set G) := by
  refine ⟨?_, hTY⟩
  intro he
  exact hH.1 (le_bot_iff.mp (he ▸ twoCore_le_of_sylow_le T hTY hYH))

/-- Every member of `H` in a simple QTKE-group is SQTK: its core normalizer
is a proper two-local subgroup containing it. -/
theorem sqtk_of_mem_H [Finite G] {K : GroupClass} (hG : IsSimpleQTKE K G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK K H := by
  have hnorm : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 H).le_normalizer_map H.subtype
  have hs := hG.twoLocal_sqtk
    (show IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) from
      ⟨H.pCoreIn 2, hH, isPGroup_pCoreIn 2 H, rfl⟩)
  exact ⟨hs.stronglyQuasithin.of_injective (inclusion hnorm) (inclusion_injective hnorm),
    hs.isKGroup.of_injective (inclusion hnorm) (inclusion_injective hnorm)⟩

/-- Every proper overgroup of `T` in a minimal outside member lies in `M`. -/
theorem HStar.proper_overgroup_le (T : Sylow 2 G) {M H Y : Subgroup G}
    (hH : H ∈ HStar (T : Subgroup G) M)
    (hTY : (T : Subgroup G) ≤ Y) (hYH : Y < H) : Y ≤ M := by
  by_contra hn
  exact hYH.not_ge (hH.2
    ⟨mem_HOver_of_sylow_interval T hTY hYH.le hH.1.1, hn⟩ hYH.le)

/-- Lemma 3.1.3(1), retaining the actual unique maximal subgroup `H ∩ M`. -/
theorem HStar.unique_maximal (T : Sylow 2 G) {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ HStar (T : Subgroup G) M) :
    (T : Subgroup G) ≤ H ⊓ M ∧ H ⊓ M ⋖ H ∧
      ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y ⋖ H → Y = H ⊓ M := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hlt : H ⊓ M < H := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hH.1.2 (he ▸ inf_le_right))
  have hcov : H ⊓ M ⋖ H := ⟨hlt, by
    intro Y hBY hYH
    exact hBY.not_ge (le_inf hYH.le (HStar.proper_overgroup_le T hH
      ((le_inf hTH hTM).trans hBY.le) hYH))⟩
  refine ⟨le_inf hTH hTM, hcov, ?_⟩
  intro Y hTY hYH
  have hYB : Y ≤ H ⊓ M := le_inf hYH.le (HStar.proper_overgroup_le T hH hTY hYH.lt)
  exact ((hYH.eq_or_eq hYB inf_le_left).resolve_right hlt.ne).symm

theorem HStar.hasUniqueMaximalOver (T : Sylow 2 G) {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ HStar (T : Subgroup G) M) :
    Order.HasUniqueMaximalOver (T : Subgroup G) H := by
  obtain ⟨hle, hc, hu⟩ := HStar.unique_maximal T hTM hH
  exact ⟨hle.trans_lt hc.lt, H ⊓ M, ⟨hle, hc⟩, fun Y hY => hu Y hY.1 hY.2⟩

/-- Lemma 3.1.3(2). The second disjunct states that the Sylow subgroup is
not normal in `H`, equivalently that `H` is not 2-closed. -/
theorem HStar.minimalParabolic (T : Sylow 2 G) {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ HStar (T : Subgroup G) M)
    (hn : normalizer (T : Set G) ≤ M ∨ ¬ ((T : Subgroup G).subgroupOf H).Normal) :
    ChapterB.IsMinimalParabolicOver T H := by
  refine ⟨HStar.hasUniqueMaximalOver T hTM hH, ?_⟩
  intro hnorm
  rcases hn with hn | hn
  · exact hH.1.2 (hnorm.trans hn)
  · exact hn ((normal_subgroupOf_iff_le_normalizer hH.1.1.2).mpr hnorm)

/-- Lemma 3.1.4, including both the equivalence and the strict intersection.
Elementary abelianness is unnecessary for this normalizer calculation. -/
theorem ti_intersection_normalizer {M H U V : Subgroup G}
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (hHU : H ≤ normalizer (U : Set G)) :
    H ⊓ M = H ⊓ normalizer (V : Set G) ∧
      (¬ H ≤ M ↔ ¬ H ≤ normalizer (V : Set G)) ∧
      (¬ H ≤ M → H ⊓ normalizer (V : Set G) < H) := by
  have he := inf_eq_inf_normalizer_of_trivial_intersections hTI hNV hU hUV hHU
  have hi : H ≤ M ↔ H ≤ normalizer (V : Set G) := by
    constructor
    · intro h
      exact (inf_eq_left.mp (he.symm.trans (inf_eq_left.mpr h)))
    · exact fun h => h.trans hNV
  refine ⟨he, not_congr hi, ?_⟩
  intro hn
  exact lt_of_le_of_ne inf_le_left (fun hh => hn (hi.mpr (inf_eq_left.mp hh)))

/-- The common-normal branch is impossible outside a unique maximal
two-local overgroup. This is the exclusion used in 3.1.8 and 3.1.9. -/
theorem no_common_normal_of_unique_maximal [Finite G]
    {A H M R : Subgroup G} (hR : IsPGroup 2 R)
    (hunique : ∀ L : Subgroup G, IsMaximalTwoLocal L → A ≤ L → L = M)
    (hHM : ¬ H ≤ M) :
    ¬ ∃ N : Subgroup G, N ≤ R ∧ N ≠ ⊥ ∧ NormalIn N (generated A H) := by
  rintro ⟨N, hNR, hn, hnormal⟩
  have hnorm := normalIn_iff_le_normalizer.mp hnormal
  rw [generated_eq_sup] at hnorm
  have hpN : IsPGroup 2 N := hR.of_injective (inclusion hNR) (inclusion_injective hNR)
  have hcore := le_pCoreIn_of_normalizes hpN hnorm.1 hnorm.2
  have hc := Theory.GroupTheory.twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup
    A H M hunique hHM
  have hb : (A ⊔ H).pCoreIn 2 = ⊥ := by rw [pCoreIn, hc, Subgroup.map_bot]
  exact hn (le_bot_iff.mp (hb ▸ hcore))

end CFSG.Quasithin.Chapter3
