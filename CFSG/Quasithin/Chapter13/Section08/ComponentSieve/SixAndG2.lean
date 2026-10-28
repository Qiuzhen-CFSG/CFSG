module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Cover
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Linear
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Actions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Filtration

/-!
# Reductions for the A₆ and G₂(2)' cases of the component sieve

Aschbacher–Smith 13.8.26 and the final paragraph of 13.8.27, printed
pp.962–963 (combined manuscript of 1 March 2004), require concrete module
and marked-parabolic calculations in addition to the critical-pair sieve.

The present development proves the linear transvection-centralizer
contradiction from explicit intrinsic model inputs, the passage of
quadratic action to an equivariant quotient, and the strict subgroup
filtration used for G₂. It also transports commutator dimensions to actual
subgroup ranks and compares the two critical subgroups using an ambient
conjugator. The A₆ cover comparison constructs an actual module equivalence
commuting with a given perfect central-cover projection.

This is not yet 13.8.26 or the G₂ exclusion. Remaining obligations include
the marked A₆ natural quotient, its perfect-cover projection, and the faithful
extension normalizer,
the strong-offender contradiction on the correct quotient of `V_H/U_H`,
the G₂ natural/Weyl alternatives, and the parabolic actor and action bounds
needed to instantiate the filtration. Earlier chapter and critical-pair
inputs, including `H = G₁ = KT` in the G₂ branch, belong to the parent
source assembly and must be supplied on the genuine subgroup sections.
-/
