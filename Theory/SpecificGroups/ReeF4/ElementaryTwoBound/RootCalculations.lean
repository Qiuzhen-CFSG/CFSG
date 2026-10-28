module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Counting
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.SectionData
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Sections
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Support
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.WordCalculations

/-!
# Assembly of the Ree root calculations from section coordinates

The square-support and commutator conclusions follow here from checked matrix
calculations. Collection in closed split-root supports supplies the supported
positive-word factorizations, and uniqueness of coordinates gives the orders of
the larger subgroup joins. Together these construct every root-calculation
clause and give the order bound for every elementary subgroup of D, with no
remaining section-coordinate or root-calculation premise.

Source: GLS3 Lemma 3.3.9, `refs/KGroup/GLS3/chapter3.tex`, pp.134–135.
-/
public section
namespace ReeF4.ElementaryTwoBound
open Subgroup RootCalculations
open NormalizedRootCentralizers.CenterExponent

/-- All root-calculation clauses, conditional only on section support and order. -/
theorem rootCalculationFacts_of_sections (m : ℕ) (h : SectionFacts m) :
    RootCalculationFacts m where
  card_D := h.card_D
  card_D₁ := h.card_D₁
  card_D₂ := h.card_D₂
  card_T₁ := h.card_T₁
  card_T₂ := h.card_T₂
  card_left := RootCalculations.card_left m
  card_right := RootCalculations.card_right m
  card_Y₁ := RootCalculations.card_Y₁ m
  card_K := h.card_K
  square_D₁ := by
    intro x hx hs
    obtain ⟨p,hp,rfl⟩ := h.support_D₁ x hx
    exact wordElement_mem_T₁ m p (square_left_support m p hp hs)
  square_D₂ := by
    intro x hx hs
    obtain ⟨p,hp,rfl⟩ := h.support_D₂ x hx
    exact wordElement_mem_T₂ m p (square_right_support m p hp hs)
  disjoint_Y₁_X₂ := RootCalculations.disjoint_Y₁_X₂ m
  cross_commute := RootCalculations.cross_commute m
  centralizer_X₂ := by
    intro e he he1 x hx
    obtain ⟨a,rfl⟩ := (mem_X_iff m 1 (by decide) e).mp he
    have ha : a ≠ 0 := by
      intro ha
      apply he1
      rw [ha]
      exact mainElement_zero m 1
    obtain ⟨p,hp,hpx⟩ := h.support_D x hx.1
    rw [← hpx]
    apply wordElement_mem_K m p
    apply centralizer_support m p hp a ha
    have hc := mem_centralizer_iff.mp hx.2 (NormalizedRootCentralizers.CenterExponent.mainElement m 1 a)
      (Set.mem_singleton _)
    change wordElement m p * _ = _ * wordElement m p
    rw [hpx]
    exact hc.symm

/-- The counting bound from any proof of the section-coordinate facts. -/
theorem card_le_in_D_of_sections (m : ℕ) (h : SectionFacts m)
    (E : Subgroup (Model m)) (hED : E ≤ D m) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 2 ^ (5 * (2 * m + 1)) :=
  card_le_in_D_of_root_calculations m (rootCalculationFacts_of_sections m h) E hED hE

/-- The literal root calculations for the second half of GLS3 Lemma 3.3.9. -/
theorem rootCalculationFacts (m : ℕ) (hm : 1 ≤ m) : RootCalculationFacts m :=
  rootCalculationFacts_of_sections m (sectionFacts m hm)

/-- Every elementary two-subgroup of the source section D has order at most
the fifth power of the coefficient-field order. -/
theorem card_le_in_D (m : ℕ) (hm : 1 ≤ m)
    (E : Subgroup (Model m)) (hED : E ≤ D m) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 2 ^ (5 * (2 * m + 1)) :=
  card_le_in_D_of_root_calculations m (rootCalculationFacts m hm) E hED hE

end ReeF4.ElementaryTwoBound
