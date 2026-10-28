module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalCentralizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction

/-!
# Group reduction in Aschbacher–Smith 13.8.25

`SourceReduction.source_linear_reduction` proves `n = 4`, `L/O₂(L) ≅ Â₆` (the triple cover),
`H/O₂(H) ≅ L₄(2)`, and `H = G₁`, starting with `K/O₂(K) ≅ Lₙ(2)`
for `3 ≤ n ≤ 5`. Source: *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, printed pp.959–960, PDF pp.976–977.

The conditional inputs are the genuine earlier local and appendix facts,
uniform 13.8.21 consequences, and the independent uniform A₇ exclusion.
The proof assembles the parabolic reduction, selects the actual maximal
quotient, excludes natural-plus-dual using the marked two-space, and proves
nontrivial component action on the maximal submodule. Both strong-offender
branches use the actual six-dimensional natural or seven-dimensional
augmentation sections and the critical centralizer to contradict six versus
five. The rank-one branch uses the larger critical actor and pointwise
centralizer rigidity. The resulting uniform reduction discharges the input
to the genuine C-component overgroup argument for `H = G₁`.

Both cases of 13.8.8 are retained. The later assertion that the entire
`Ũ_H` is natural belongs to the separate FourStructure argument.
-/
