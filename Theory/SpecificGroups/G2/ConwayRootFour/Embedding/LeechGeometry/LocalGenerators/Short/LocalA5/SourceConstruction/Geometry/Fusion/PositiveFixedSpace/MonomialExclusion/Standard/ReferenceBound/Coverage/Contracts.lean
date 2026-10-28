module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Coverage.ColumnData

/-!
# Two independent exhaustive checks after the centralizer normal form

`ColumnCoverage` must exhaust all involutive column maps satisfying the actual
hexacode-generator equations. `SignedCoverage` must exhaust every translation
and every even column-sign vector for each proposed column map. The latter can
be proved independently of the former: its quantified input is the explicit
sixteen-entry table, not an asserted classification of column maps.

Both obligations are genuine finite mathematics. They assert coverage, not just
validity of listed candidates. The original 512-entry table is unchanged.
Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Atlas.Codes
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage

/-- Exhaustiveness of the proposed column table under the literal generator tests. -/
def ColumnCoverage : Prop :=
  ∀ pi : HexIndex → HexIndex, ColumnChecks pi → ∃ q : Fin 16, pi = columnCandidate q

/-- Both literal parameters, using exactly the parent's `flat` indexing. -/
def ParameterMatches (pi : HexIndex → HexIndex) (u : HexParameters)
    (r : Fin 5 → Bit) (k : Fin 512) : Prop :=
  (∀ i, signedWord pi u r (StandardCoordinates.flat.symm i) = candidateSign k i) ∧
  (∀ i, StandardCoordinates.flat (markedPull pi (hexEncoder u)
      (StandardCoordinates.flat.symm i)) = candidatePull k i)

/-- Exhaust all eleven binary parameters for each listed column map. -/
def SignedCoverage : Prop :=
  ∀ (q : Fin 16) (u : HexParameters) (r : Fin 5 → Bit),
    Function.Involutive (markedPull (columnCandidate q) (hexEncoder u)) →
    (∀ i, signedWord (columnCandidate q) u r i +
      signedWord (columnCandidate q) u r
        (markedPull (columnCandidate q) (hexEncoder u) i) = 0) →
    ∃ k : Fin 512, ParameterMatches (columnCandidate q) u r k

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound.Coverage
