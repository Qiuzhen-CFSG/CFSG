module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Involutions
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Assembly
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.TransportedGeometry

/-!
# Intrinsic local geometry of the binary SL₅ exterior square

This interface uses the actual determinant-one action on Λ²(F₂⁵). It exports
lexicographic wedge coordinates, the standard subspaces V₁, V₃, V₄, V₆, V₇,
the complete natural flag, its stabilizers, and the last-column shear subgroup.
The four exterior stabilizers are the corresponding flag parabolics. Their
two-cores, solvable residuals and actual Levi quotients are identified, with
genuine natural and orthogonal module equivalences and the chief filtration
0 < V₁ < V₇ < V. The two involution classes have natural displacement ranks
one and two and exterior ranks three and four; C_V(j₁) = V₄ + V₆.

There are exactly two point orbits. The second-point stabilizer is a split
extension of the actual R₆ = O₂(L₆T) by S₆. Its fixed spaces and the precise
A₂/A₃ fixed-space comparisons are established using last-column shears.
The complementary-wedge equivalence transports geometry to the exterior cube
along inverse transpose, including literal invariant subquotients.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §12.5,
printed pp.817–821/PDF pp.834–838, Lemmas 12.5.2 and 12.5.5 and the intrinsic
module calculations in 12.5.7/10. No ambient QTKE or classification hypotheses
are used. Source module recognition and ambient fusion remain with their
chapter owners.
-/
