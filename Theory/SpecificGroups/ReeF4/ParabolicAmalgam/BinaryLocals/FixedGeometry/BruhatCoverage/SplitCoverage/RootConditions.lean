module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitGeneration
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Collection

/-!
# Root relations needed for binary split Bruhat coverage

These two local conditions concern the actual root matrices: filtered exchanges
between positive roots and conjugation by a simple Weyl word. They are the
binary specializations of GLS3 1.12.1(b,h), in
`refs/KGroup/GLS3/Chapter1.tex`. Neither asserts a global factorization.
The coverage assembly must supply proofs of both conditions.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RadicalCoordinates

/-- The positive-support, binary specialization of filtered matrix exchanges. -/
def BinaryPositiveRootExchanges : Prop :=
  ∀ (r s : Root .positive) (a b : CoefficientField 0), r ≠ s →
    ∃ correction : List (Root .positive × CoefficientField 0),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootGeneratorInGroup 0 r.val a * rootGeneratorInGroup 0 s.val b =
        rootGeneratorInGroup 0 s.val b * rootGeneratorInGroup 0 r.val a *
          FilteredCollection.wordProduct
            (fun q : Root .positive => rootGeneratorInGroup 0 q.val) correction

/-- In characteristic two the signs in simple Weyl conjugation disappear. -/
def BinarySimpleRootConjugation : Prop :=
  ∀ (i : Fin 4) (r : F4Chevalley.Root) (t : CoefficientField 0),
    simpleWord 0 [i] * rootGeneratorInGroup 0 r t * (simpleWord 0 [i])⁻¹ =
      rootGeneratorInGroup 0 (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t

end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
