module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.LocalExtension
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.StandardLocalExtensions
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryExtensionExclusion

/-!
# Automorphism-extension calculations for the split G₂ model

The actual coefficientwise field action is faithful and outer in
characteristic two. For finite fields of order greater than two,
`semilinearEquiv` identifies the full automorphism group with the semidirect
product of the actual model and its coefficient field automorphisms.
`fieldComponent` has precisely the inner automorphisms as its kernel.

The short and long standard local quotient maps onto the actual PSL₂(F)
intertwine coefficient transport. Their kernels are the respective five-root
radicals. The concrete field extensions have exactly these radicals as their
two-cores, and an element inducing an inner quotient automorphism has trivial
field part. The general conditional local-extension interfaces are preserved;
the standard-local applications discharge their quotient and kernel premises.

For the binary model, `binaryAutomorphismEquiv` identifies full G₂(2) with
Aut(G₂(2)′) by literal conjugation, preserving both marked parabolic types.
The full model of order 12096 and its derived subgroup of order 6048 remain
distinct. Full G₂(2) is complete; a faithful extension acting on its derived
subgroup has no further elements, and its two marked parabolics and whole
overlap are exactly the original images (`binaryExtension_marked_eq`).

These are the family automorphism inputs to F.1.12. The ambient weak-BN-pair
argument that eliminates extensions for q > 2 belongs to the source assembly.

Source: Aschbacher--Smith, F.1.12, printed pp.263--264, and the extension and
Dynkin-action convention in Definition F.4.3, printed p.274.
-/
