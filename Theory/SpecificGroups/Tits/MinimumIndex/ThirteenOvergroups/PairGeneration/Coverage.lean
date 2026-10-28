module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Representatives
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.FactorsLow
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.FactorsHigh
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Geometry

/-!
# Coverage by the fixed thirteen-normalizer double cosets

Every element of the actual ATLAS group lies in a double coset of the literal
thirteen-normalizer through one of the 3010 fixed representatives.

The checked point witnesses reduce the problem to 32 point fibers. The checked
stabilizer transitions cover each fiber by 144 normalizer cosets. Combining the
two factor-row certificates checks all 4608 remaining products, and the reduction
then gives unconditional coverage. Both factors belong to the actual normalizer;
neither its exact order nor disjointness of the double cosets is needed.

Source: the primary ATLAS Tits generators. Provenance and reproduction are in
`Coverage/source/README.md`; the fixed representative words remain unchanged.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration

/-- All 4608 reduced products pass the fixed normalizer-factorization test. -/
public theorem CoverageCertificate.factors_checked (i : Fin 32) (j : Fin 144) :
    CoverageCertificate.factorTest i j = true := by
  by_cases hi : i.val < 16
  · exact CoverageCertificate.factors_low_checked i hi j
  · exact CoverageCertificate.factors_high_checked i (Nat.le_of_not_gt hi) j

/-- The fixed 3010 representatives cover all double cosets of the actual
thirteen-normalizer, with no additional certificate premises. -/
public theorem normalizer_doubleCoset_cover (x : Atlas1600Group) :
    ∃ (a b : thirteenNormalizer) (k : Fin 3010),
      x = a.val * representative k * b.val :=
  CoverageCertificate.coverage_of_finite_checks
    CoverageCertificate.points_checked CoverageCertificate.transitions_checked
    CoverageCertificate.factors_checked x

end Tits.MinimumIndexThirteen.PairGeneration
