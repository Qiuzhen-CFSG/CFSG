module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.PairCubic
public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.LiteralPairs

/-!
# The signed pair construction for the monomial Griess summands

The actual action on Parker coordinate halfspaces supplies a common marked
coordinate permutation of `N`, with its generator formulas and its comparison
with `NaturalAction`. Its signed symmetric tensors give `pairRepresentation`
on three zero-diagonal symmetric matrix spaces, trivial on `K`.

The pair trace form and the explicit triangle/mixed-pair cubic are invariant.
`literalPair` indexes the fixed off-diagonal matrix, `wPlus`, and `wMinus`
generators in `ESpace`. The identification with these literal Griess summands,
the local `C` compatibility, and the calculation identifying the pair cubic
with the existing `griessBeta` are additional mathematical comparisons.

Source: Aschbacher, *Sporadic Groups*, 27.4, 29.4, 29.10–29.11, printed
pp. 146, 155, 158–160. Product order is explained in `EAction.Transport`.
-/
