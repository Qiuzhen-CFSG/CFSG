module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.CoveredParameters
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.LieParameters
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.SmallModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.SporadicModels

/-!
# Assembly of the signed model intersection

The complete action list from 1.1.5 is split here, retaining the actual
quotient by the two-core. The Lie-type branch needs only evenness of the
supplied signed parameter: simplicity then lifts the given model. The
central-cover branch requires a comparison of its simple quotient with
PSL₃(4) and G₂(4); its conclusion retains the cover. Trivial odd core removes
the alternating triple covers before the remaining small and sporadic
carrier comparisons are applied.

`intersection` discharges all four comparison premises of the preserved
`intersection_of_carrier_comparisons` interface using the concrete carrier
proofs. Two-rank bounds and defining-prime divisibility recover evenness
in every simple Lie alternative. Rank and order obstructions eliminate
the remaining small and sporadic alternatives and identify the signed
parameter in the central-cover branch. The original sign and exact field
order are retained; no recognition from equal orders is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2)
(printed pp.51--52), 1.1.5(3) (pp.501--503), and the uses on pp.1135, 1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
open Chapter1.Section02.LocalModels ClassificationModels ComponentStructure
universe u

/-- Exhaustive assembly from four genuine carrier-comparison theorems.
Every extra premise must be discharged before using this as the source
model intersection. The exceptional conclusion keeps the original two-core. -/
theorem intersection_of_carrier_comparisons
    (hLie : ∀ (S : Type u) [Group S] [Finite S] [IsQuasisimple S],
      IsSimpleGroup S → LieTypeTwoModel S → primeRank 3 S = 2 →
      ∀ (unitary : Bool) (q : ℕ), q % 3 = (if unitary then 2 else 1) →
        IsPSLSign S unitary 3 q → Even q)
    (hCover : ∀ (S : Type u) [Group S] [Finite S] [IsQuasisimple S] [IsSimpleGroup S],
      (ClassicalGroup.IsPSL S 3 4 ∨ IsG2At S 4) →
      ∀ (unitary : Bool) (q : ℕ), q % 3 = (if unitary then 2 else 1) →
        IsPSLSign S unitary 3 q →
        unitary = false ∧ q = 4 ∧ ClassicalGroup.IsPSL S 3 4)
    (hSmall : ∀ (S : Type u) [Group S] [Finite S] [IsQuasisimple S],
      pPrimeCore 2 S = ⊥ → primeRank 3 S = 2 →
      (IsAlternating S 6 ∨ IsAlternating S 7 ∨ ClassicalGroup.IsPSL S 3 3 ∨
        ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL S 2 p) →
      ∀ (unitary : Bool) (q : ℕ), q % 3 = (if unitary then 2 else 1) →
        IsPSLSign (S ⧸ pCore 2 S) unitary 3 q → False)
    (hSporadic : ∀ (S : Type u) [Group S] [Finite S] [IsQuasisimple S] [IsSimpleGroup S],
      ∀ name : SporadicName, name ≠ .j3 → Nonempty (S ≃* name.Carrier) →
      ∀ (unitary : Bool) (q : ℕ), q % 3 = (if unitary then 2 else 1) →
        IsPSLSign S unitary 3 q → False)
    {K : Type u} [Group K] [Finite K] [IsQuasisimple K]
    {α : MulAut K} (hmodel : ModelAction115 K α)
    (hodd : pPrimeCore 2 K = ⊥) (hrank : primeRank 3 K = 2)
    {unitary : Bool} {q : ℕ} (hmod : q % 3 = (if unitary then 2 else 1))
    (hsigned : IsPSLSign (K ⧸ pCore 2 K) unitary 3 q) :
    (∃ n : ℕ, 0 < n ∧ q = 2 ^ n ∧ IsPSLSign K unitary 3 (2 ^ n)) ∨
      (unitary = false ∧ q = 4 ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) := by
  let := twoCore_quotient_simple hodd
  let := twoCore_quotient_quasisimple hodd
  cases hmodel with
  | lie hs hm _ =>
    let := hs
    exact Or.inl (simple_binary_conclusion hsigned
      (hLie K hs hm hrank unitary q hmod (signed_lift_of_simple hsigned)))
  | two_cover _ _ hm _ =>
    exact Or.inr (hCover (K ⧸ pCore 2 K) hm unitary q hmod hsigned)
  | six _ _ ha =>
    exact (hSmall K hodd hrank (Or.inl (alternating_model_of_action hodd ha))
      unitary q hmod hsigned).elim
  | seven _ _ ha =>
    exact (hSmall K hodd hrank (Or.inr (Or.inl (alternating_model_of_action hodd ha)))
      unitary q hmod hsigned).elim
  | odd hm _ =>
    exact (hSmall K hodd hrank (Or.inr (Or.inr hm)) unitary q hmod hsigned).elim
  | sporadic name hn hm _ =>
    exact (hSporadic (K ⧸ pCore 2 K) name hn hm unitary q hmod hsigned).elim

/-- Intersect the complete 1.1.5 action list with the signed projective model
in A.3.18(2). The original component is the supplied signed group over a
positive binary field, or its two-core quotient is precisely PSL₃(4).
The latter alternative retains all permitted central two-covers. -/
theorem intersection
    {K : Type u} [Group K] [Finite K] [IsQuasisimple K]
    {α : MulAut K} (hmodel : ModelAction115 K α)
    (hodd : pPrimeCore 2 K = ⊥) (hrank : primeRank 3 K = 2)
    {unitary : Bool} {q : ℕ} (hmod : q % 3 = (if unitary then 2 else 1))
    (hsigned : IsPSLSign (K ⧸ pCore 2 K) unitary 3 q) :
    (∃ n : ℕ, 0 < n ∧ q = 2 ^ n ∧ IsPSLSign K unitary 3 (2 ^ n)) ∨
      (unitary = false ∧ q = 4 ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) := by
  exact intersection_of_carrier_comparisons lie_parameters
    CoveredParameters.covered_parameters small_models_excluded
    SporadicModels.sporadic_separation hmodel hodd hrank hmod hsigned

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
