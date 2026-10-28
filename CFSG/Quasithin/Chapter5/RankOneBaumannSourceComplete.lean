module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceGeneration

/-!
# The rank-one Baumann bound from earlier source uniqueness

The centralizing and natural branches are already proved on the original Input.
In the A5 branch the local five-point action gives elementary crossing cores,
then generating cores, then the actual central elementary factor and two D8
factors. The odd residual of the Baumann normalizer preserves the original core,
so uniqueness over LT finishes the normalizer bound.

The point-centralizer input in the crossing argument follows from source 4.3.2,
uniqueness over L. It remains explicit here. Its earlier-source owner is
qt-d-1222-rankone-global-uniqueness; that owner's existing ChosenModule and
Hypothesis1223 contract must be extended to the original Input used here.
This module does not assert the unconditional 5.1.7(1).

Source: Aschbacher--Smith 4.3.2, p.613, and 5.1.7(1), pp.633--634.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- All local A5 calculations are discharged. Only the earlier point-centralizer
control remains explicit. -/
theorem Input.baumann_normalizer_of_point_centralizers
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : ∀ x ∈ ChapterB.baumann (T : Subgroup G) ⊓ centralizer (L : Set G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨g,hg,hQ,hcross,hgen⟩ := h.exists_baumann_generated_elementary_core hout hc
  exact h.baumann_normalizer_of_generated_elementary_cores hout hQ g hg hcross hgen

/-- The exact earlier uniqueness implication consumed by the point argument.
The chosen original module and every original Input hypothesis are retained. -/
theorem Input.baumann_normalizer_of_source_uniqueness
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hu : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  apply h.baumann_normalizer_of_point_centralizers
  intro x hx hne
  have hp : IsPGroup 2 (zpowers x) := T.isPGroup'.to_le (zpowers_le.mpr hx.1.1)
  have hNZ : normalizer (zpowers x : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal hu hp
      (fun he => hne (zpowers_eq_bot.mp he))
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hx.2 l hl)
  rw [←centralizer_closure,←zpowers_eq_closure]
  exact (Subgroup.centralizer_le_normalizer _).trans hNZ

/-- Only the A5 block branch needs uniqueness over L; the other original
source branches are already closed without this earlier premise. -/
theorem Input.baumann_normalizer_of_alternating_uniqueness
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hu : ChapterC.IsAlternatingBlock L 5 →
      ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  exact hout (h.baumann_normalizer_of_source_uniqueness
    (hu (h.alternating_block_of_baumann_escape hout).2.1))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
