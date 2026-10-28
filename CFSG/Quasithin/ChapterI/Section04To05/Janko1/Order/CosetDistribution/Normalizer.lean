module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Setup
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCountReduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenStructure
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts

/-!
# Normalizer conclusions for Bender's J₁ count

The Sylow normalizer has order 168 from the original local hypotheses.
For an order-seven subgroup, the source counts in its centralizer's
normalizer imply that it is self-centralizing whenever its own normalizer
has even order. In the contrary case, the local structure theorem constructs
the cyclic complement of order six, and the incidence argument supplies
the literal coset counts. Their counting contradiction completes (4.3).
The final theorem assembles both conclusions from the original centralizer
data and the earlier odd-prime local results in `BenderPrimeData`.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4 and (4.3), printed pp.225–226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- Conditional assembly: the two source normalizer conclusions follow
once the contrary-case counts in `N_G(C_G(S))` have been constructed. -/
public theorem bender_normalizerData_of_seven_counts {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d)
    (counts : ∀ S : Subgroup G, S ≤ normalizer (h.sylow : Set G) →
      Nat.card S = 7 → Even (Nat.card (normalizer (S : Set G))) →
      centralizer (S : Set G) ≠ S → BenderSevenCountData S) : BenderNormalizerData h := by
  refine ⟨h.sylow_normalizer_card, ?_⟩
  intro S hSN hS hEven
  by_contra hne
  exact hne (h.seven_centralizer_eq_of_counts localData S hS (counts S hSN hS hEven hne))

/-- The Sylow normalizer has order 168, and every order-seven subgroup
of it with even-order ambient normalizer is self-centralizing, as in
Bender (4.3). The local structure and coset counts in the contrary case
are constructed from the earlier odd-prime local data. -/
public theorem bender_normalizerData {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) : BenderNormalizerData h := by
  apply h.bender_normalizerData_of_seven_counts localData
  intro S hSN hS hEven hne
  obtain ⟨structureData⟩ := h.bender_seven_structure localData S hSN hS hEven hne
  exact h.bender_seven_counts localData S hSN hS hEven hne structureData

end CFSG.Quasithin.Janko1CentralizerData
