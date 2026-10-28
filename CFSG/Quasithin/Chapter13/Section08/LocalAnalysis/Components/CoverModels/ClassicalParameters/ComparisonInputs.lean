module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels

/-!
# Remaining comparisons for odd-prime degree-three groups

These are explicit proof obligations, not assertions that the families are
disjoint. All predicates retain actual multiplicative equivalences. The
prime bound excludes the genuine overlap PSU₃(3) ≃ G₂(2)′; the parent
proves this bound from the source cover's center of order three.

The Bender and rank-two comparisons are independent. Their proofs can use
simplicity and perfectness inherited from the source central quotient.
Source: Aschbacher–Smith, A.3.6(2), printed p.43; F.9.18(4), pp.325–326;
and 13.8.17, p.953.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
open Subgroup Theory.GroupTheory
open Chapter1.Section02.LocalModels Models
universe u

/-- The remaining odd-prime comparison against all three genuine Bender families. -/
def OddBenderComparison (S : Type u) [Group S] : Prop :=
  ∀ (unitary : Bool) (p : ℕ), p.Prime → Odd p → 5 ≤ p →
    IsPSLSign S unitary 3 p → ¬ ClassificationModels.IsBenderModel S

/-- The remaining odd-prime comparisons against the actual rank-two carriers.
The commutator subgroups include the parameter-two endpoints. -/
def OddRankTwoComparison (S : Type u) [Group S] : Prop :=
  ∀ (unitary : Bool) (p : ℕ), p.Prime → Odd p → 5 ≤ p →
    IsPSLSign S unitary 3 p → ∀ (n : ℕ), 1 ≤ n →
      (¬ ClassicalGroup.IsPSL S 3 (2 ^ n)) ∧
      (¬ IsSp4DerivedAt S (2 ^ n)) ∧ (¬ IsG2DerivedAt S (2 ^ n))

end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
