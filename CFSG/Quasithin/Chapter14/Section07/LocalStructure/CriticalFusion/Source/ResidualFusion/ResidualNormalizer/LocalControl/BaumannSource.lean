module

public import CFSG.Quasithin.Chapter12.Section08.Setup.Normalizers
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Defs

/-!
# The characteristic-subgroup alternative in 14.7.10

For the original higher-rank source, let S = Baum(R₁). If a nontrivial
characteristic subgroup C of S is normal in LT, then N_G(S) normalizes C.
The full earlier uniqueness theorem on LT places N_G(C) inside N_G(L).
Every subgroup, inclusion and normalizer is in the original ambient group.

This proves the first-branch application of C.1.37 used in 14.7.10. It does
not assert the existence of C or the alternative chief-factor bound; those
require the source pushing-up classification. Structural1222 and
Uniqueness127 are the genuine earlier universal source implications.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 14.7.10,
printed p.1045, using alternative (1) of C.1.37, pp.141–143.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {κ : GroupClass.{u}}

/-- The actual source characteristic obstruction gives the normalizer
conclusion of 14.7.10, without a local normalizer-bound premise. -/
theorem baumann_normalizer_le_of_characteristic_normal
    (h : HigherRankHypothesis κ T L V 3)
    (structural : Chapter12.Section02.Structural1222 κ)
    (uniqueness : Uniqueness127 κ) (F : InvariantFlag T V 3)
    (C : Subgroup (ChapterB.baumann (F.Ri L 1)))
    (hC : C.Characteristic) (hne : C ≠ ⊥)
    (hn : ((C.map (ChapterB.baumann (F.Ri L 1)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal) :
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  let S := ChapterB.baumann (F.Ri L 1)
  let D := C.map S.subtype
  have hDLT : D ≤ L ⊔ (T : Subgroup G) := by
    apply (map_subtype_le C).trans
    apply (show S ≤ F.Ri L 1 from inf_le_left).trans
    exact (pCoreIn_le 2 _).trans (sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl)
  have hLN : L ⊔ (T : Subgroup G) ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDLT).mp hn
  have hN : normalizer (D : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro M hM hLM
      exact Set.mem_singleton_iff.mp ((h.maximal_unique structural uniqueness).2 ▸
        show M ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hM, hLM⟩)
    · exact (((isPGroup_pCoreIn 2 _).to_le (show S ≤ F.Ri L 1 from inf_le_left)).to_subgroup C).map S.subtype
    · exact fun hz => hne ((C.map_eq_bot_iff_of_injective S.subtype_injective).mp hz)
    · exact hLN
  let := hC
  exact (normalizer_le_normalizer_characteristic_image S C).trans hN

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
