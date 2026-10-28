module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Descent

/-!
# The odd triality fundamental subgroup and its complementary residual

`Descent` fixes the actual central-root subgroup in the graph-field carrier,
constructs elementary lifts from pinned rank-one maps, and records the exact
central quotient kernels. A faithful commuting cubic-field map gives both
properness of the fundamental subgroup and rank at least `3 * P.exponent`
in its literal prime-to-p residual centralizer. Centralizer exhaustion upgrades
that map to an equivalence, and the common scalar determines the exact factor
intersection.

The odd pinned maps and the root-matrix centralizer calculations remain
explicit premises. Their construction and final assembly are not yet supplied
by this module.

Sources: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), and
Aschbacher–Smith, Lemma A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/
