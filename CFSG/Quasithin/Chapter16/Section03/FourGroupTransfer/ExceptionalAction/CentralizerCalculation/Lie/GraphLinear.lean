module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.GraphLinear.Reduction

/-!
# Assembly reductions for the linear and unitary graph pairs

The source exclusion uses the absence of a subgroup of order four in the
full pointwise fixer. For graph-fixed PSL₂ the fixer can have an odd part,
so a bound on its total order is not required. The faithful order-four
actor contradicts the intrinsic nondivisibility calculation. This gives the
strict bounds in the requested `LieBounds` fields without changing them.

For the covering row, the actual image of L is a component in the full
fixed subgroup downstairs and retains its PSL₂ model. The central cover
is preserved, and faithful automorphism descent supplies divisibility.

The theorems here are conditional assembly reductions. The three intrinsic
nondivisibility calculations in their hypotheses still require proofs;
these reductions do not establish the two unconditional `LieBounds` fields.

Source: Aschbacher–Smith 16.1.4(5–6), 16.1.7(3b–c), and 16.3.5,
combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory GraphLinear
universe u
variable {G : Type u} [Group G] [Finite G]
variable {E L I : Subgroup G} {t i : G}

/-- Conditional assembly of the graph-field linear row from its intrinsic
calculation on the actual component of an involution fixed subgroup. -/
theorem pairFixer_card_lt_four_graph_field_linear_of_calculation
    (hcalc : ∀ (S : Type u) [Group S] [Finite S] [IsQuasisimple S]
      (n : ℕ), 1 < n → ClassicalGroup.IsPSL S 3 (2 ^ (2 * n)) →
      ∀ (P : Subgroup S), ClassicalGroup.IsPSU P 3 (2 ^ n) →
      ∀ (a : MulAut S), orderOf a = 2 → IsComponentIn P a.fixedSubgroup →
        ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut S) (P : Set S)))
    (h : PairContext E L I t i) (n : ℕ) (hn : 1 < n)
    (hlarge : ClassicalGroup.IsPSL I 3 (2 ^ (2 * n)))
    (hsmall : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    Nat.card (pairFixer L I) < 4 := by
  let := h.component.quasisimple
  have hsmall' := hsmall.of_mulEquiv (subgroupOfEquivOfLe h.proper.le)
  exact (hcalc I n hn hlarge (L.subgroupOf I) hsmall'
    h.involutionAction h.involutionAction_orderOf h.component_in_action_fixed
    (four_dvd_pairFixer h)).elim

/-- Conditional assembly of both graph rows, retaining the covering kernel
and the embedding of L in the actual two-core quotient. -/
theorem pairFixer_card_lt_four_graph_linear_unitary_of_calculations
    (hlinear : ∀ (S : Type u) [Group S] [Finite S] [IsQuasisimple S]
      (n : ℕ), 1 < n → ClassicalGroup.IsPSL S 3 (2 ^ n) →
      ∀ (P : Subgroup S), ClassicalGroup.IsPSL P 2 (2 ^ n) →
      ∀ (a : MulAut S), orderOf a = 2 → IsComponentIn P a.fixedSubgroup →
        ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut S) (P : Set S)))
    (hunitary : ∀ (S : Type u) [Group S] [Finite S] [IsQuasisimple S]
      (n : ℕ), 1 < n → ClassicalGroup.IsPSU S 3 (2 ^ n) →
      ∀ (P : Subgroup S), ClassicalGroup.IsPSL P 2 (2 ^ n) →
      ∀ (a : MulAut S), orderOf a = 2 → IsComponentIn P a.fixedSubgroup →
        ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut S) (P : Set S)))
    {𝒦 : GroupClass.{u}} (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) (n : ℕ) (hn : 1 < n)
    (hlarge : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSU (I ⧸ pCore 2 I) 3 (2 ^ n))
    (hsmall : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    Nat.card (pairFixer L I) < 4 := by
  let := core_quotient_quasisimple hG h
  have hsmall' := corePairComponent_isPSL_two hG h hsmall
  have ha := coreAction_orderOf hG h
  have hcomponent := component_in_coreAction_fixed hG h
  have hdiv := four_dvd_corePairFixer hG h
  rcases hlarge with hlarge | hlarge
  · exact (hlinear (I ⧸ pCore 2 I) n hn hlarge _ hsmall' _ ha hcomponent hdiv).elim
  · exact (hunitary (I ⧸ pCore 2 I) n hn hlarge _ hsmall' _ ha hcomponent hdiv).elim

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
