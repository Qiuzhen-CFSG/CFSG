module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.MarkingFacts
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks

/-!
# Placement of odd-index {2,3}-subgroups of Held

Every odd-index subgroup whose prime divisors are two and three is conjugate
into one of the two literal ATLAS max3/max4 subgroups. The marked two-group
can be conjugated into any odd-index subgroup. Exhaustive double-coset
factorization and the representative obstruction checks then put that subgroup
inside the union of the two aligned local subgroups, hence inside one of them.

This module supplies all four concrete premises of `placement_of_tests` from
the checked marking, transition columns and representative tests. The source
adapter supplies the remaining index and prime-divisor hypotheses for the
actual permuting Sylow pair. No maximal-subgroup catalogue is assumed.

Sources: Aschbacher–Smith, printed pp.509–511; Aschbacher, *Overgroups of
Sylow subgroups in sporadic groups* (1986); GLS3 Table 5.3p. The literal words
and their ATLAS provenance are preserved in the imported calculation modules.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups

/-- Exhaustive placement for odd-index subgroups with only the prime divisors
two and three, using the certified calculations in the actual Held carrier. -/
public theorem placement (K : Subgroup He) (hindex : ¬ 2 ∣ K.index)
    (hprimes : ∀ p : ℕ, Nat.Prime p → p ∣ Nat.card K → p = 2 ∨ p = 3) :
    ∃ (i : Bool) (g : He),
      K.map (MulAut.conj g).toMonoidHom ≤ localOvergroup i :=
  placement_of_tests markedSubgroup_isPGroup markedSubgroup_le_aligned
    DoubleCosets.covers representativeChecks K hindex hprimes

end Held.LocalPairs.PairCoverage.SylowOvergroups
