module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusion
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicAssembly

/-!
# The prime-order consumer after the fixed-layer exclusion

The fixed-layer proof removes the elementary-square alternative. Two source
obligations remain: reduction of the extraspecial case to p=d=3 and |W|=64,
and the terminal binary-three module/core contradiction. This module assembles
those implications and applies the resulting primeStep to the published
cyclic local analysis on the same subgroups. It asserts neither outstanding
source obligation. Their final discharge remains with the 12.2.23 owner.

Source: Aschbacher--Smith, 12.2.23, printed pp.803--804.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}

/-- Assembly of 12.2.23 from the two remaining extraspecial source arguments.
The numerical reduction and the terminal module/core argument are still explicit. -/
theorem prime_order_of_extraspecial_steps
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (S : InvariantOddLocalAnalysis T L V d p H P U W g v) (hnone : NoEscape L V)
    (numerical : IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 ∧ d = 3 ∧ Nat.card W = 64)
    (terminal : IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 → False) : Nat.card P = p := by
  by_contra hne
  obtain ⟨he, hc, hx, hf⟩ := S.extraspecial_of_card_ne_prime D A hnone hne
  obtain ⟨hp, hd, hw⟩ := numerical he hc hx hf
  exact terminal he hc hx hf hp hd hw

/-- The literal `primeStep` application in the published cyclic analysis.
All extra premises are confined to the two remaining extraspecial source proofs;
the invariant odd-subgroup and block producers retain their original interfaces. -/
theorem cyclicLocalAnalysis_of_extraspecial_steps
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hnone : NoEscape L V) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (oddStep : ∃ p H P U W g v, InvariantOddLocalAnalysis T L V d p H P U W g v)
    (numerical : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 ∧ d = 3 ∧ Nat.card W = 64)
    (terminal : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 → False)
    (blockStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p →
      ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V →
      ChapterC.IsLinearTwoBlock L d) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  apply cyclicLocalAnalysis_of_invariant_odd_steps hTV oddStep _ blockStep
  intro p H P U W g v S
  exact prime_order_of_extraspecial_steps D A S hnone
    (numerical p H P U W g v S) (terminal p H P U W g v S)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
