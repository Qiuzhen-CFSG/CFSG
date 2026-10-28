module

public import Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates.Roots
public import Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates.WeylTorus

/-!
# Fourteen coordinates for the actual G₂ adjoint representation

For every field of characteristic two, `Coordinates.equiv` identifies all
Leibniz derivations of the literal split-octonion product with `Fin 14 → F`.
Its inverse is the explicit linear map `Coordinates.fromParams`. Reconstruction
proves surjectivity and dimension fourteen. The transported action is intertwined
with actual octonion-automorphism conjugation by `Coordinates.repEquiv`.

The six `action_root*` formulas hold at every field parameter. The two
`action_weyl*` formulas and `action_torus` use the actual Weyl and torus elements.
The coordinate order is fixed by the matrix entries
`(1,7), (2,7), (4,7), (5,6), (5,7), (6,5), (6,6), (6,7),
 (7,1), (7,2), (7,4), (7,5), (7,6), (7,7)`, with output row first.

Source: GLS3, Examples 1.14.9(c) and 2.8.10(g), using the attributed ATLAS
split-octonion model. Irreducibility and highest-weight assertions are separate
results; this interface establishes the actual carrier and coordinate action.
-/
