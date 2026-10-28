module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearEndgame
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.SourceAssembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.TransvectionSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.Strict
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource

/-!
# Alternating and binary-linear branches of the component sieve

Aschbacher–Smith 13.8.24 excludes `K* ≅ A₇`. Lemma 13.8.25 says that
`K/O₂(K) ≅ Lₙ(2)`, for `3 ≤ n ≤ 5`, forces `n = 4`, `L/O₂(L) ≅ Â₆`,
`H* ≅ L₄(2)`, the four-dimensional natural action on `Ũ_H`, and `H = G₁`.
Source: *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), printed pp.958–962, PDF pp.975–979.

`SourceAssembly.not_alternatingSeven_uniform` proves the conditional A₇
exclusion on every relevant local overgroup, using both actual permutation
partitions. `SourceAssembly.source_linear_alternative` proves all the linear
conclusions, including an equivariant linear equivalence for the entire
natural module and the equality H = G₁.

`TransvectionSource` derives the full center-quotient models and the weaker
seven-point sieve models from the actual 13.8.5 recognition theorem. Its
`source_linear_alternative_of_transvection` supplies the first-case linear
conclusion without the strict-case chief-factor and splitting premises.
The earlier local, 13.7.6 and G.6.4 inputs remain explicit.

`LinearReduction.OriginalSource` constructs the original group and overgroup
inputs, supplies the uniform A₇ exclusion, and connects both whole-module
branches. Its original middle-node argument constructs the critical geometry
and literal quotient and applies the proved marked B.4 classifications.
`OriginalSource.source_linear_alternative` retains only the genuine preceding
source and component conclusions.

The proof retains both cases of 13.8.8, the L₃/L₅ and orthogonal S₈
exclusions, and the L₄ chief-factor, cohomology, splitting and cyclic/noncyclic
arguments. The complete earlier 13.8.5 model alternatives supply the
transvection case; uniform 13.8.24 feeds the genuine C-component overgroup
argument. The chapter consumer still supplies the explicit preceding local
and appendix facts, including 13.8.21–23. Final 13.8.27 assembly belongs to
that consumer.
-/
