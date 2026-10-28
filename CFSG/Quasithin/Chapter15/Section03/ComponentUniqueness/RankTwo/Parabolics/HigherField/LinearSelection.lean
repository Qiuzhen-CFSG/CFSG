module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.LinearSelection.Parity
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.LinearSelection.Ree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.LinearSelection.Exceptional

/-!
# Selecting the even-degree linear family in the larger-field branch

Odd-degree PSL₃ and the Ree family are excluded by their three-free
Borels, transported through the central two-kernel of the original
component. The other alternatives, symplectic four, G₂ and triality,
have cyclic outer automorphism groups by the actual model coverage
theorems. That cyclicity contradicts the full S₃ × S₃ Borel shadow.

The final theorem proves the family-selection sentence on p.1139:
L⁺ is PSL₃(2ⁿ) for even n > 1. It uses only the component setup, the
genuine family alternative and Borel containment. Neither the later
field restriction n = 2 nor any multiplier theorem is assumed. The
earlier partial reduction is preserved as a separate public theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final proof
of 15.3.35, printed p.1139, using 15.3.33, 15.3.36 and 15.3.41.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField
variable {G : Type*} [Group G] [Finite G]

/-- The two Borel-order exclusions, leaving precisely the three families
whose automorphism actions must still be ruled out. -/
theorem larger_field_linear_or_remaining
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hfamily : LargerFieldRankTwoModel (componentImage I L L))
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B) :
    (∃ n : ℕ, 1 < n ∧ Even n ∧ ClassicalGroup.IsPSL (componentImage I L L) 3 (2^n)) ∨
    (∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSp (componentImage I L L) 2 (2^n)) ∨
    (∃ n : ℕ, 1 < n ∧ ClassificationModels.IsG2At (componentImage I L L) (2^n)) ∨
    (∃ n : ℕ, 1 < n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (componentImage I L L)) := by
  cases hfamily with
  | linear n hn hmodel =>
      exact Or.inl ⟨n, hn,
        LinearSelection.even_degree_of_linear_component I L M Yplus S B c hB hYB hmodel,
        hmodel⟩
  | symplectic n hn hmodel => exact Or.inr (Or.inl ⟨n, hn, hmodel⟩)
  | g2 n hn hmodel => exact Or.inr (Or.inr (Or.inl ⟨n, hn, hmodel⟩))
  | triality n hn hmodel => exact Or.inr (Or.inr (Or.inr ⟨n, hn, hmodel⟩))
  | ree m _ hmodel =>
      exact (LinearSelection.not_ree_component I L M Yplus S B c hB hYB hmodel).elim

/-- The family-selection sentence in the larger-field paragraph of 15.3.35.
All non-linear alternatives are excluded through their actual models; the
linear Borel calculation forces even degree. -/
theorem larger_field_linear_even
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hfamily : LargerFieldRankTwoModel (componentImage I L L))
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B) :
    ∃ n : ℕ, 1 < n ∧ Even n ∧ ClassicalGroup.IsPSL (componentImage I L L) 3 (2 ^ n) := by
  rcases larger_field_linear_or_remaining I L M Yplus S B c hfamily hB hYB with
    hlinear | ⟨n, hn, hmodel⟩ | ⟨n, hn, hmodel⟩ | ⟨n, hn, hmodel⟩
  · exact hlinear
  · exact (LinearSelection.CyclicOuter.false_of_symplectic
      I L M Yplus S B c hB hYB n hn hmodel).elim
  · exact (LinearSelection.false_of_g2 I L M Yplus S B c hB hYB n hn hmodel).elim
  · exact (LinearSelection.false_of_triality I L M Yplus S B c hB hYB n hn hmodel).elim

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField
