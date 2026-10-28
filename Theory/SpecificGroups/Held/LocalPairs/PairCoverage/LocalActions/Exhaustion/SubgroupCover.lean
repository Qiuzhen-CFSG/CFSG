module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.CoverageReduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Transitions
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.RepresentativeChecks

/-!
# Assembly of the Held local subgroup cover

This extension assembles the certified literal finite checks with the complete
subgroup argument. Positive right-coset transitions give exhaustive coverage;
alignment and the prime-five row obstructions then prove containment in one
of the two published products. The temporary two-group hypothesis is the only
remaining input: initial conjugation takes place inside the local overgroup,
using the subgroup's odd relative index. The parent exhaustion assembly can
discharge that hypothesis from the candidate orders.

Sources: Aschbacher–Smith, printed pp.509–511; GLS3 Table 5.3p; the literal
ATLAS local words and SubgroupCover/source/Generate.g.
-/

public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
open SubgroupCover

/-- Assembly from explicit finite word checks, retained as a reusable reduction. -/
theorem localProductCover_of_finite_checks
    (hmark : ∀ i : Bool, IsPGroup 2 (candidateTwo i 0))
    (hsteps : PositiveTransitions)
    (halign : ∀ i j, candidateTwo i 0 ≤ alignedProduct i j)
    (hrows : ∀ i r, representative i r ∈ alignedProduct i 0 ∨
      representative i r ∈ alignedProduct i 1 ∨ orderOf (obstruction i r) = 5) :
    LocalProductCover :=
  localProductCover_of_certificates hmark
    (doubleCosetCoverage_of_transitions hsteps) halign hrows

/-- Every odd-index subgroup of either literal local overgroup whose prime
divisors are two or three is locally conjugate into a published candidate
product. All finite certificates are discharged; only the marked candidates'
two-group property remains for the parent exhaustion assembly. -/
theorem localProductCover_of_isPGroup
    (hmark : ∀ i : Bool, IsPGroup 2 (candidateTwo i 0)) :
    LocalProductCover :=
  localProductCover_of_finite_checks hmark positiveTransitions
    marked_le_aligned representative_alternative

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
