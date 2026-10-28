module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.NormIdeal
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Image
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Data
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.KernelCube

/-!
# Finite algebra inputs for the normalized M₁₁ involution

`pointRepresentation_asAlgebraHom_surjective` and
`referenceKernel_cube_le_elevenIdeal` prove both finite-algebra inputs to
`exists_equiv_of_algebra_certificate` in `NormalizedInvolution`.

The norm-reduction certificate supplies a surjective coordinate lift modulo
the actual two-sided norm ideal. Its certified three-layer filtration has
the actual point representation on every diagonal copy. Each reference-kernel
element lowers this filtration, so every product of three lies in the norm
ideal. The full-image theorem uses irreducibility and Jacobson density.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359,
citing James, J. Algebra 27 (1973), 57–111.
-/
