module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.OrbitTools
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.AssemblyTools
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.Certificates

/-!
# Normalized generator pairs on Held's first involution class

A certified generator-closed family of 24990 actual Held words contains every
conjugate of `a`. For exponents 1 and 3, each row either moves a point under
source relator 1 or 3, or has the three literal marked fixed-point equations.
Thus the original hypothesis imposing all seven relators implies `PairFixes`.
No group-order, simplicity, perfectness, presentation-isomorphism or index
assumption is used.

Source: John Bray's `Held/Model/Source/HeG1-P1.M`, its seven uncommented
relators and `M1`; the retained `HeG1-p2058B0.g1/.g2` permutation tables.
Magma conjugation `x^y = y⁻¹*x*y` is retained. The generator tables are
inverted when converting the source right actions to Lean left actions.
`ClassA/Source/generate.py` reproduces the untrusted witnesses; all generator
closure edges and row tests are certified by Lean kernel reduction.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs

/-- Every normalized pair satisfying the seven source relators whose first
entry is conjugate to `a` has the required marked fixed point, for 1 and 3. -/
public theorem classCalculation_a : ClassCalculation a :=
  ClassA.classCalculation_of_facts (ClassA.facts_of_blocks ClassA.allBlocks)

end Held.Realization.MarkedConjugacy.NormalizedPairs
