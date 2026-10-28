module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalControl
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.Restriction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.PairGeometry

/-!
# Local geometry for Aschbacher's minimal counterexample

The current exports prove the unique fixed-coset assertion (c), pair permutation
for incomparable factors, and existence of local Sylow subgroups with ambient
image in H. Nested factors already satisfy global strong closure by normalizer
ascent. The complete `MinimalCounterexample.localControl` assembly still needs
pair permutation in the nested minimal-counterexample case and the centralizer
induction after a justified Sylow reselection.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(b)--(d), printed pp.94--95, DOI 10.1215/ijm/1256050927.
-/
