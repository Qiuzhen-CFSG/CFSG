module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.JankoLocal.Reduction
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.SmallPrimes

/-!
# Outer oddness and local normalization for swapped J₁

Every automorphism of the actual matrix model is inner by the completed
`JankoOne` certificate. The genuine outer quotient therefore has order one.
An actual multiplicative equivalence transports this to Q, yielding the
oddness needed in the outer-action obstruction on printed p.510.

The checked bounds for normalizers of subgroups of orders 3, 5, 7, 11 and 19
discharge the local premises of the solvable Fitting argument. Every solvable
overgroup of a Sylow two-subgroup in J₁ therefore normalizes that subgroup.
Transport along the actual model equivalence and through both projections
gives normalization in Q × Q. This holds for every subgroup with solvable
join, and hence for the odd-prime subgroup in the source application.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.510; GLS3 Table 5.3f, Out(J₁) = 1.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

private theorem janko_one_prime_normalizer_bounds (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    Janko1.LocalStructure.PrimeNormalizerBound p :=
  Janko1.LocalStructure.primeNormalizerBound_of_cases
    Janko1.LocalStructure.primeNormalizerBound_three
    Janko1.LocalStructure.primeNormalizerBound_five
    Janko1.LocalStructure.primeNormalizerBound_seven
    Janko1.LocalStructure.primeNormalizerBound_eleven
    Janko1.LocalStructure.primeNormalizerBound_nineteen hp ho

/-- Every solvable overgroup of a Sylow two-subgroup in an actual J₁ model
normalizes that Sylow subgroup. -/
public theorem janko_one_model_solvable_overgroup_le_normalizer
    {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* Janko1.Model)
    (S : Sylow 2 Q) (H : Subgroup Q) [Group.IsSolvable H]
    (hSH : (S : Subgroup Q) ≤ H) : H ≤ Subgroup.normalizer (S : Set Q) :=
  janko_one_model_solvable_overgroup_le_normalizer_of_prime_bounds
    janko_one_prime_normalizer_bounds e S H hSH

/-- The J₁ product normalization used on printed p.510. The odd-prime
subgroup case follows from this result for every subgroup with solvable join. -/
public theorem janko_one_model_prod_le_normalizer
    {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* Janko1.Model)
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ Subgroup.normalizer (S : Set (Q × Q)) :=
  janko_one_model_prod_le_normalizer_of_prime_bounds janko_one_prime_normalizer_bounds e S A

/-- The actual outer group of a group isomorphic to J₁ has order one. -/
public theorem janko_one_outer_card_eq_one {Q : Type*} [Group Q]
    (e : Q ≃* Janko1.Model) : Nat.card (MulAut.Outer Q) = 1 := by
  let _ := Janko1.OuterCertificate.outer_subsingleton
  let _ : Subsingleton (MulAut.Outer Q) := (MulAut.outerCongr e).injective.subsingleton
  exact Nat.card_unique

/-- The odd outer order used to exclude J₁ in the swapped-component case. -/
public theorem janko_one_outer_odd {Q : Type*} [Group Q]
    (e : Q ≃* Janko1.Model) : Odd (Nat.card (MulAut.Outer Q)) := by
  rw [janko_one_outer_card_eq_one e]
  decide

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
