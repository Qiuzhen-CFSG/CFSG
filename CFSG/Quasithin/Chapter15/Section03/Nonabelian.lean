module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.FixedLine
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Transfer

/-!
# The nonabelian conjugate-closure case of Section 15.3

Theorem 15.3.50 says that `⟨V^H⟩` is abelian for every member `H` of
`H(T,M)`. A counterexample reduces to `H = M_c = C_G(Z)`. The source
then studies `U = ⟨Z_S^H⟩` and its genuine conjugation quotient `U/Z`.

The imported constructions distinguish that quotient from `H/O₂(H)`
and fix the almost-special pairs used in 15.3.54–56. `FixedLine` proves
the generation, cardinality, and irreducibility deduction in 15.3.57(1)
from the paired-actor fixed-point calculation. `Transfer` proves the
final contradiction from the index and two-class fusion assertions.

The configuration 15.3.51–56, the actual recognition and module
decomposition 15.3.57(2)–58, and the core and fusion assertions
15.3.59–61 remain necessary. No theorem named 15.3.50 is asserted until
these inputs have been discharged from the preceding local conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1145–1151.
-/
