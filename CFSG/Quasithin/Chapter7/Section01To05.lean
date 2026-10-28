module

public import CFSG.Quasithin.Chapter7.Section01To05.M23GlobalBounds

/-!
# Weak-closure eliminations in §§7.1–7.5

This assembly currently supplies the actual fixed-space/dual-core bridge,
the weak-closure parameter deductions, the equality-case subgroup argument,
and both marked Mathieu applications. The M₂₃ application includes an
unconditional proof of the native H.16.8 span bound from existing geometry
and checked fixed-space calculations. The literal index-two inverse-image
family now supplies all clauses of 7.5.3. The marked M₂₃ code exclusion
requires only the global bounds w ≤ 2 and r ≥ 6; its local two-rank and
fixed-span premises are discharged, and a local m bound is unnecessary.

The source case catalogue 7.1.1, representation table 7.2.1, Cartan bound
7.3.4 and global lower bounds 7.3.2/7.4.1 are still obligations. In particular
the explicit hypotheses in the elimination lemmas must be derived from the
genuine Fundamental Setup and Hypotheses 7.0.2/7.3.1 before claiming the
source theorem 7.5.4. No group-family tag or numerical record stands in for
those missing source implications.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§§7.1–7.5, printed pp.696–700 (PDF pp.713–717).
-/
