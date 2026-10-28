module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.Basic
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Collection

/-!
# Local root relations for split F₄ normal forms

The positive-root relation is the height-filtered Chevalley exchange law.
The negative-simple relation concerns multiplication of a single normalizer
cell by one root element. Together they suffice for normal forms, by word
induction and collection. Neither condition asserts coverage of the group.
The nonzero rank-one words in `splitNormalizerWords` retain torus factors.

These are explicit intermediate proof obligations for GLS3 1.11.5 and
1.12.1, `refs/KGroup/GLS3/Chapter1.tex`. The final split coverage theorem must
discharge them; root transport alone is not asserted to prove either one here.
-/

@[expose] public section
noncomputable section

namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.RadicalCoordinates LargeLocalSeeds
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Adjacent positive-root exchanges, with corrections of strictly greater height. -/
def PositiveRootExchanges (m : ℕ) : Prop :=
  ∀ (r s : Root .positive) (a b : CoefficientField m), r ≠ s →
    ∃ correction : List (Root .positive × CoefficientField m),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootGeneratorInGroup m r.val a * rootGeneratorInGroup m s.val b =
        rootGeneratorInGroup m s.val b * rootGeneratorInGroup m r.val a *
          FilteredCollection.wordProduct
            (fun q : Root .positive => rootGeneratorInGroup m q.val) correction

/-- Local cell exchange for a negative simple root, allowing torus factors
in the resulting normalizer word. This is a local multiplication law. -/
def NegativeSimpleExchange (m : ℕ) : Prop :=
  ∀ (i : Fin 4) (t : CoefficientField m) (u : SplitGroup m),
    u ∈ splitUnipotent m → ∀ n ∈ splitNormalizerWords m,
      ∃ a ∈ splitUnipotent m, ∃ n' ∈ splitNormalizerWords m,
        ∃ c ∈ splitUnipotent m,
          rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t * u * n = a * n' * c

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
