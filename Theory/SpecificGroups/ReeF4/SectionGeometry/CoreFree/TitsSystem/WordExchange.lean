module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.Nontriviality
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.Reduction
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.BorelFactorization
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.RankOneGauss
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.BlockSign

/-!
# Concrete Ree orbit-word calculations

`weylLift_borel_conjugation_witness` proves nontriviality of each actual
relative reflection, unconditionally over every coefficient field.
`word_exchange_of_monomial` proves exchange assuming precisely the Weyl-monomial
presentation and height-triangular kernel facts for the split normalizer words.
It collects the full fixed Borel with its simple relative block last, applies
the proved rank-one Gauss decomposition in the opposite-sign case, and uses
exceptional duality to determine the sign of the entire block. Every positive
B₂ root and the full fixed torus are retained.

These are the concrete word calculations; unconditional Tits-system assembly
still belongs to the parent and must supply the two normalizer matrix facts.

Source: GLS3 2.3.4(b), 2.3.5 and §2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry

/-- Concrete relative exchange, with only the two permitted split-normalizer
matrix hypotheses. The calculation also covers the binary endpoint. -/
theorem word_exchange_of_monomial (m : ℕ)
    (hweyl : ∀ n ∈ splitNormalizerWords m,
      ∃ (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ),
        RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c)
    (hkernel : ∀ n ∈ splitNormalizerWords m,
      Overlap.IsHeightTriangular n → n ∈ diagonalTorus m) :
    ∀ s : Side, ∀ n ∈ normalizerWords m, ∀ b ∈ borel m,
      weylLift m s * b * n ∈ borelCell m (weylLift m s * n) ∪ borelCell m n :=
  word_exchange_of_root_factors m (borelSimpleFactorization m) (relativeRankOneGauss m)
    (relativeBlockSign_of_monomial m hweyl hkernel)

end ReeF4.SectionGeometry.BNPair
