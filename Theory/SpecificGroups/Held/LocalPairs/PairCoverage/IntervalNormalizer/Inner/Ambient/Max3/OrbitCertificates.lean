module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitData
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates.Label0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates.Label1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates.Label2
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates.Label3
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates.Label4
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates.Label5
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.OrbitCertificates.Label6
import Mathlib.Tactic.FinCases

/-!
# Actual orbit sizes for all seven max3 interval entries

The finite certificates prove that each candidate component is invariant under
all eight Schreier words and has a rooted spanning tree consisting of those
words. Hence each component is exactly an orbit of the actual word-generated
subgroup. Kernel-checked counts identify its cardinality with `orbitSizeLabel`.
No simplicity, self-normalization, or representative-orbit premise is needed.

Sources: the unchanged ATLAS HeG1-p2058B0/max3 permutations and the representative
words underlying the max3 calculation accompanying GLS3 Table 5.3p. The existing
`Source/orbits.json` partitions are reproduced and certified by the data in
`OrbitCertificates`; the parent selection and geometry modules are unchanged.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3

/-- The published size label is the cardinality of the actual selected entry's
orbit in Held's degree-2058 action, for every one of the seven entries. -/
public theorem orbitSizeLabel_eq_card_orbit (t : Fin 7) (x : Fin 2058) :
    orbitSizeLabel t x = Nat.card (MulAction.orbit (selectedEntry t) x) := by
  fin_cases t
  · exact OrbitCertificates.label_eq_card OrbitCertificates.Label0.valid x
  · exact OrbitCertificates.label_eq_card OrbitCertificates.Label1.valid x
  · exact OrbitCertificates.label_eq_card OrbitCertificates.Label2.valid x
  · exact OrbitCertificates.label_eq_card OrbitCertificates.Label3.valid x
  · exact OrbitCertificates.label_eq_card OrbitCertificates.Label4.valid x
  · exact OrbitCertificates.label_eq_card OrbitCertificates.Label5.valid x
  · exact OrbitCertificates.label_eq_card OrbitCertificates.Label6.valid x

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
