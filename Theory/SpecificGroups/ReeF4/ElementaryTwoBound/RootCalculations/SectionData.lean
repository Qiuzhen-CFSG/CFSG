module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Curves

/-!
# Remaining section-coordinate inputs for the Ree counting argument

The three support clauses assert actual positive-word factorizations of the
literal subgroup joins. The order clauses count the six larger sections. The
endpoint orders, square detection, cross-commutator calculation and centralizer
coordinate detection are proved independently and consumed in `RootCalculations`.
No clause assumes an elementary-subgroup order bound or a square/centralizer
conclusion. The construction of these inputs remains a separate obligation.

Source: GLS3 Lemma 3.3.9, `refs/KGroup/GLS3/chapter3.tex`, pp.134–135.
The coefficient-field order is GLS's q².
-/
public section
namespace ReeF4.ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent

/-- Literal support and order facts needed to finish the source root calculations. -/
structure SectionFacts (m : ℕ) : Prop where
  support_D : ∀ x ∈ D m, ∃ p : PositiveParameters m, DSupport p ∧ wordElement m p = x
  support_D₁ : ∀ x ∈ D₁ m, ∃ p : PositiveParameters m, D₁Support p ∧ wordElement m p = x
  support_D₂ : ∀ x ∈ D₂ m, ∃ p : PositiveParameters m, D₂Support p ∧ wordElement m p = x
  card_D : Nat.card (D m) = (2 ^ (2 * m + 1)) ^ 9
  card_D₁ : Nat.card (D₁ m) = (2 ^ (2 * m + 1)) ^ 7
  card_D₂ : Nat.card (D₂ m) = (2 ^ (2 * m + 1)) ^ 7
  card_T₁ : Nat.card (T₁ m) = (2 ^ (2 * m + 1)) ^ 5
  card_T₂ : Nat.card (T₂ m) = (2 ^ (2 * m + 1)) ^ 5
  card_K : Nat.card (K m) = (2 ^ (2 * m + 1)) ^ 8

end ReeF4.ElementaryTwoBound.RootCalculations
