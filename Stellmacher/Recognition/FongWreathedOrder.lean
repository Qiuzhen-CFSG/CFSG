module

public import Stellmacher.Recognition.FongWreathedOrderCandidates
public import Stellmacher.Recognition.FongWreathedFiveOrderExclusion
public import Stellmacher.Recognition.FongWreathedSevenBlockExclusion

/-!
# Fong's order reduction

The character-degree bounds, self-centralizing seven subgroup and the three
numerical order candidates are re-exported here. The final assembly excludes
18144 by the cyclic seven-block argument and 90720 by the five-centralizer and
cyclic five-block arguments of Fong (1967), printed pp.74–75.
-/

public section
noncomputable section
namespace Stellmacher.Recognition.FongWreathed
open FongWreathedExceptional
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Fong's order reduction: the Sylow-seven subgroup supplied by the degree-seven
character is self-centralizing and the ambient simple group has order `6048`.

The two other numerical candidates are excluded by the cyclic seven-block and
the five-centralizer/block arguments, respectively. -/
theorem exists_seven_subgroup_card_eq_6048
    (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2) (x : G)
    (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ Z : Subgroup G, Nat.card Z = 7 ∧
      Subgroup.centralizer (Z : Set G) = Z ∧ Nat.card G = 6048 := by
  obtain ⟨P, d, hc⟩ := FongWreathedExceptional.exists_characters S hS x hx
  obtain ⟨c⟩ := hc
  obtain ⟨χ₇, hχ₇, hdeg₇, hrat₇, hinv₇⟩ := c.degree_seven_character
  have hSCard : Nat.card S = 32 := by simpa using P.card
  obtain ⟨T, hT, hC, hcases⟩ := sylow_seven_order_candidates S hSCard
    hχ₇ hdeg₇ hrat₇ hinv₇ c.order_lower
  have hG : Nat.card G = 6048 := by
    rcases hcases with ⟨h6048, _⟩ | ⟨h18144, hindex⟩ | ⟨h90720, _⟩
    · exact h6048
    · exfalso
      let χ₂₇ := c.rational.χ₂
      have hχ₂₇ : IsIrreducibleCharacter χ₂₇ := c.rational.irreducible.1
      have hdeg₂₇ : χ₂₇ 1 = 27 := c.degree_twenty_seven
      have hrat₂₇ : ∀ g : G, ∃ q : ℚ, χ₂₇ g = (q : ℂ) := by
        intro g
        obtain ⟨z, hz⟩ := c.rational.integer_values.1 g
        exact ⟨z, by simpa using hz⟩
      exact (order_ne_18144_of_rational_degree_twenty_seven T hT hC hindex
        hχ₂₇ hrat₂₇ hdeg₂₇) h18144
    · exfalso
      exact (not_card_90720_of_wreathed S hS x hx) h90720
  exact ⟨(T : Subgroup G), hT, hC, hG⟩

/-- The ambient order in Fong's reduction. -/
theorem card_eq_6048
    (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2) (x : G)
    (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nat.card G = 6048 := by
  obtain ⟨_, _, _, hG⟩ := exists_seven_subgroup_card_eq_6048 S hS x hx
  exact hG

end Stellmacher.Recognition.FongWreathed
