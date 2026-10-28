module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28

/-!
# The actual Sylow/core normalization for 4.2.3

A.4.2 makes O₂(LT) Sylow in the section centralizer. Maximality identifies
it with C_T(L/O₂(L)). Conjugating the original Sylow by the already selected
section-centralizer element then gives exactly the selected R-plus. Thus the
original T and the conjugator remain explicit, rather than assuming the
maximal counterexample core lies in the unaltered original Sylow.

Source: Aschbacher--Smith, Hypothesis 4.2.3 and 4.2.12, pp.608,610.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]

/-- The source two-core is exactly the centralizer of the component section in T. -/
theorem core_eq_sectionCentralizer {T : Sylow 2 G} {L : Subgroup G}
    (hp : IsPPerfect 2 L) (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = sectionCentralizerIn (T : Subgroup G) L := by
  have hS0 := ChapterA.Section04.sylow_core_sectionCentralizer T L hp hn
  rw [←sectionCentralizerIn_eq_twoSectionCentralizer] at hS0
  obtain ⟨S,hS⟩ := hS0
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hC : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      sectionCentralizerIn (normalizer (L : Set G)) L := hS ▸ map_subtype_le _
  have hQC : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ sectionCentralizerIn (T : Subgroup G) L :=
    le_inf hQ (hC.trans inf_le_right)
  have hs := Chapter1.isSylowIn_iff.mp (show Chapter1.IsSylowIn 2
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (sectionCentralizerIn (normalizer (L : Set G)) L) from ⟨S,hS⟩)
  exact (hs.2.2 _ (T.isPGroup'.to_le inf_le_left) hQC
    (le_inf (inf_le_left.trans hn) inf_le_right)).symm

/-- Conjugating the original Sylow inside the section centralizer realizes
exactly the selected R-plus, without replacing the original T. -/
theorem aligned_sylow_core {T : Sylow 2 G} {L : Subgroup G}
    (hp : IsPPerfect 2 L) (hn : (T : Subgroup G) ≤ normalizer (L : Set G))
    (c : sectionCentralizerIn (normalizer (L : Set G)) L) :
    (L ⊔ ((c : G) • T : Sylow 2 G)).pCoreIn 2 =
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom ∧
    (L ⊔ ((c : G) • T : Sylow 2 G)).pCoreIn 2 =
      sectionCentralizerIn (((c : G) • T : Sylow 2 G) : Subgroup G) L := by
  have hL : L.map (MulAut.conj (c : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hTc : (((c : G) • T : Sylow 2 G) : Subgroup G) ≤ normalizer (L : Set G) := by
    change (T : Subgroup G).map (MulAut.conj (c : G)).toMonoidHom ≤ _
    exact (map_mono hn).trans (by rw [map_equiv_normalizer_eq,hL])
  refine ⟨?_,core_eq_sectionCentralizer hp hTc⟩
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj (c : G)).injective,Subgroup.map_sup,hL]
  rfl
end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
