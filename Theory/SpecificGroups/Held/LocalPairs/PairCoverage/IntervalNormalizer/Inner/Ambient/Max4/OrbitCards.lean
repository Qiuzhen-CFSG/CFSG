module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Row0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Row1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Row2
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Row3
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Row4
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Row5
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Row6

/-!
# Exact orbit sizes for the seven Held max4 entries

All seven literal eight-generator Schreier closures are certified. Each row
checks invariance under all generators, reachability by a spanning forest,
and the cardinality of every component. The checked action is the original
Held degree-2058 action conjugated by the inverse of `conjugator 3`.

Sources: GLS3 Table 5.3p; unchanged ATLAS HeG1-p2058B0 and max4 words;
`Max4/Source/orbits{1,2,3,12,13,14,15}.json`. The JSON and Python computations
supply candidates only; all used identities and counts are kernel checked.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4

/-- The stored labels are the cardinalities of the actual candidate orbits. -/
public theorem orbitSizeLabel_eq_card_orbit (j : Fin 7) (x : Fin 2058) :
    orbitSizeLabel j x = Nat.card (MulAction.orbit (candidate j) x) := by
  fin_cases j
  · exact OrbitCards.Row0.card x
  · exact OrbitCards.Row1.card x
  · exact OrbitCards.Row2.card x
  · exact OrbitCards.Row3.card x
  · exact OrbitCards.Row4.card x
  · exact OrbitCards.Row5.card x
  · exact OrbitCards.Row6.card x

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
