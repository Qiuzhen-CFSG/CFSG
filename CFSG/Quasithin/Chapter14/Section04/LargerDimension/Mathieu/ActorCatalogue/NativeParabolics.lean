module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Cubic
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Residuals

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Assembly

/-!
# Native residual actors and parabolics in the Mathieu extension

The first actor is the cubic scalar subgroup. For a nonzero binary point and
a supplied index-three Borel containing S and centralizing that point,
`exists_native_parabolics` constructs the other minimal parabolic and exhausts
the literal X-family by its three pairwise distinct residual actors.

The actual join S ∨ A₂ ∨ A₃ is the full native preimage of a marked hexad
stabilizer. Its two-core is elementary abelian of order sixteen and maps
isomorphically onto the pointwise hexad kernel. Its core quotient maps onto S₆
with the cubic scalar kernel retained; the full even inverse image is the
marked nonsplit quasisimple triple cover of A₆. Explicit conjugation and
quotient maps identify the overlap A₁ ∨ A₂ ∨ S modulo its two-core with S₃ × S₃.

This completes the native group calculation used in Aschbacher--Smith 14.4.12,
printed pp.1011--1012, with 14.4.2(6) and H.12.1. Construction of the actual
Borel, lifting to H, and the module calculation identifying Y remain with
their respective source-assembly owners.
-/
