module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Signatures
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.Row8
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.Row10
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.Row16
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.Row18
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.Row19

/-!
# Five intrinsic Held subgroup reconstructions

Each row is exhaustively enumerated by products of its published generators.
Kernel-checked permutation multiplication proves closure, and four-point
separation proves injectivity. Fixed-point counts inspect all 2058 vertices;
for the two order-32 rows, the enumeration transports the overlap count to
32 indices. Explicit products prove both containments in each reconstruction.

These identities discharge the five signature premises of the E64 normalizer
reduction. They require no simplicity, group-order or graph hypotheses, and
assert no unproved centralizer or maximal-normalizer classification.

Sources: ATLAS HeG1-p2058B0, the unchanged catalogue words, GLS3 Table 5.3p;
Aschbacher–Smith condition E, printed pp.3–4 and 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment

public theorem fixedPointSpan_ambient8_eq_ambient3 :
    fixedPointSpan (ambient 8) 42 = ambient 3 := Reconstructions.Row8.reconstruction

public theorem fixedPointSpan_ambient10_eq_ambient1 :
    fixedPointSpan (ambient 10) 42 = ambient 1 := Reconstructions.Row10.reconstruction

public theorem fixedPointSpan_ambient16_eq_ambient3 :
    fixedPointSpan (ambient 16) 42 = ambient 3 := Reconstructions.Row16.reconstruction

public theorem overlapSpan_ambient18_eq_ambient5 :
    overlapSpan (ambient 18) 0 = ambient 5 := Reconstructions.Row18.reconstruction

public theorem overlapSpan_ambient19_eq_ambient3 :
    overlapSpan (ambient 19) 6 = ambient 3 := Reconstructions.Row19.reconstruction

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment
