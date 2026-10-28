module
public import Theory.GroupAction.FixedFreeA4PlaneTransport

/-!
# The fixed-free A4 plane-normalizer obstruction

This entry point exposes the nonsolvability criterion for an actual
A4 action on an elementary abelian group W of order sixteen. A cubic
fixes only the identity, a nontrivial involution fixes a subgroup C of
order four, and the supplied automorphism subgroup contains a mover of C.
The conclusion concerns that same automorphism subgroup.

The transport module preserves W, the literal automorphisms and C while
choosing binary coordinates. The shared matrix certificates and the
actual derived-series argument prove the finite obstruction. This is the
generic interface consumed by the native normalizer witnesses in
Stellmacher (8.6)(b3), Journal of Algebra 190 (1997), printed p.44.
-/
