module

public import Theory.GroupTheory.FiniteSubgroupFiltration
public import Theory.GroupAction.NormalClosureOrbitEscape

/-!
# F.7: Coset geometries and amalgam methodology

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Section F.7, printed pp.310--315. The proof of
F.7.13(2) and Lemma F.7.14 continue onto p.315.

The current imports provide two independent ingredients: finite descending
subgroup filtrations stabilize, giving the existence of a last fixed radius
once the geometric kernel is known to vanish; and normal-closure generation
with an index-two normal kernel gives an orbit point with stabilizer of index
two. The latter applies to the action on conjugates of V_beta in F.7.13(1).

The coset-geometry construction, local-core propagation, critical-pair results,
and the application of E.1 and E.2 remain separate assembly obligations. These
general lemmas do not assert the hypotheses or conclusions of those results.
-/
