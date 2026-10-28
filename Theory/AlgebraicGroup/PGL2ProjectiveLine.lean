module

public import Theory.AlgebraicGroup.Bor1.OppositePairPGL2OpenCell

/-!
# The algebraic PGL2 projective-line model

This assembly module exports the reusable rank-one model over an algebraically
closed field.  Its affine algebraic group is the tensor-image carrier
`pgl2Variety`, whose rational points are canonically identified with
`Matrix.ProjGenLinGroup (Fin 2) k`.  The scheme-backed projective line comes
with its two affine charts, and faithfully flat descent of the standard `SL2`
action supplies a genuine regular `PGL2` action with the expected action on
projective points.

The stabilizers of zero and infinity give the standard opposite Borels.  The
projected upper and lower root curves and the diagonal torus have closed
images, satisfy the regular and singular rank-one matrix identities, and give
the open-cell factorization with scalar-invariant uniqueness.  Thus consumers
can use the concrete projective geometry without assuming an `SL2` morphism
from an arbitrary algebraic group.

The projective-space and chart construction is the standard Proj model.  The
action and rank-one formulas follow Borel, *Linear Algebraic Groups*, Section
7.2 and Sections 13.13--13.14; the affine carrier is the tensor realization of
projective special linear groups used in GLS3, Example 1.1.7.
-/
