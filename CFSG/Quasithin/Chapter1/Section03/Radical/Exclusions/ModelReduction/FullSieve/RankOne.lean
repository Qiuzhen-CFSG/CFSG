module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.StarTransport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.ExceptionalG2

/-!
# Removing the fixed exceptional models from the rank-one sieve

The imported group comparisons use only concrete quotient equivalences
and their orders. They are independent of the Chapter 15 configuration.
The even exponent in the swapped model supplies their parameter-three
input, so they apply unchanged in the present radical argument.

All block alternatives except the binary natural block and the A₅-block
are excluded. The binary-linear star alternatives are excluded only after
transport through the actual core-to-star isomorphism. The full SL₃(2ⁿ)
star alternative remains explicit; its rank-one overlap is a separate
model comparison. No source classification is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.2.7(3), printed pp.145–147; proof of 1.3.8, p.514.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
open Subgroup Theory.GroupTheory
open Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases

variable {G : Type*} [Group G]

/-- The fixed exceptional models leave exactly the two possible block
types and the full even-field SL₃ star model. The latter is retained as
a conclusion, not assumed to be a rank-one group without comparison. -/
theorem ModelCases.rankOne {p : ℕ} {H₀ K R : Subgroup G}
    (hc : ModelCases H₀ K R) (hRK : R ≤ normalizer K)
    (hq : IsQuasisimple (XiQuotient K)) (hb : StarKernelBound K R)
    (hm : XiEmbedding.SwappedModel p (XiQuotient K)) :
    (ChapterC.IsBlock (K.subgroupOf H₀) ∧ ∃ n, ChapterC.IsL2EvenBlock K n) ∨
    (ChapterC.IsBlock (K.subgroupOf H₀) ∧ ChapterC.IsAlternatingBlock K 5) ∨
    IsSLThreeEven (starImage K R K) := by
  have hs := swappedModel_three hm
  cases hc with
  | binary hblock hmodel => exact Or.inl ⟨hblock, hmodel⟩
  | alternating n hlo hhi hblock hmodel =>
    obtain rfl := alternatingBlock_degree hlo hhi hmodel hs
    exact Or.inr (Or.inl ⟨hblock, hmodel⟩)
  | ahatSix hmodel => exact (not_exceptionalAhat6Block hs hmodel).elim
  | exceptionalSeven hmodel => exact (not_exceptionalA7Block hs hmodel).elim
  | symplecticFour hmodel => exact (not_sp4FourBlock hs hmodel).elim
  | binaryG2 hmodel => exact (not_binaryG2Derived_quotient hs hmodel).elim
  | linearThree hmodel => exact Or.inr (Or.inr hmodel)
  | binaryLinear n hn hmodel =>
    have hstar := swappedModel_star hRK hq hb hs
    exact (not_binaryLinear_quotient hn hstar hmodel).elim

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
