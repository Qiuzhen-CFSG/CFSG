module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Data
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives.Case0
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives.Case1
public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Representatives.Case2

/-!
# The four genuine representative contraction histograms

For representatives 1, 2 and 8, the descendants certify the coefficients of the
actual alternating quartic and 1024 rank witnesses for each representative.
Reversible row operations and diagonal factorizations prove every matrix rank;
the matrix/linear-map comparison then transfers the finite counts to the genuine
contraction image dimensions. The zero representative follows by linearity.

The four expected profiles and representatives are the ones discovered by
`BinaryQuarticMathieu/source/generate_orbits.py`. This theorem assumes no orbit,
preservation, rank-table or group-identification assertion.
-/

public section
namespace BinaryQuarticMathieu.RankRecognition

/-- Exact contraction histograms at all four representatives, including zero
entries at every other natural rank. -/
theorem representative_histograms : ∀ c : Fin 4,
    rankDistribution quartic (decode (representative c)) = profile c := by
  intro c
  fin_cases c
  · exact representative_zero_distribution
  · exact Representatives.Case0.histogram
  · exact Representatives.Case1.histogram
  · exact Representatives.Case2.histogram

end BinaryQuarticMathieu.RankRecognition
