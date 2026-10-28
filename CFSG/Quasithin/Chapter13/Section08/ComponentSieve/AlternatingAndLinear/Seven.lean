module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.ConjugateObstruction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Terminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeQuadratic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsExclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.SourceExclusion

/-!
# The seven-point branch of the component sieve

This development supplies the actual two partition stabilizers, the even
four-plus-three two-core, the conjugated transvection obstruction, the
rank-one calculation for elementary transvection actors, and the pointwise
centralizer contradiction on the actual submodule and quotient sections.
Every natural-module input is an injective equivariant map for the same
faithful seven-point group action.

The local geometry constructs the compatible action from K/O₂(K) ≅ A₇,
excludes case (1) of 13.8.8 and gives both relative partition placements.
`PairsExclusion.exclude_pair_partition` closes the three-pairs case from
explicit earlier inputs, deriving nontrivial K-action and rank one before
applying 13.8.23(4). `FourThreeQuadratic` proves the remaining partition's
quadratic rank calculation using its literal Klein four two-core.

`SourceExclusion.not_alternatingSeven` completes the conditional 13.8.24
assembly. It constructs the action and both partition placements, selects
the natural quotient from the genuine alternatives, transports the reciprocal
transvection, and derives both contradictions. Its `Earlier` input lists
the precise preceding source and universal appendix facts still supplied by
the chapter consumer. `not_alternatingSeven_original` transfers this result
through the 13.8.16 reduction to each original local overgroup.

The legacy `FourThreeSourceInput` and its dimension-twelve `HasFourDualModel`
remain for compatibility. The source assembly uses the proved natural-selection
and reciprocal-actor developments with the genuine dimension-eight alternative.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959, PDF pp.975–976 (1 March 2004 manuscript).
-/
