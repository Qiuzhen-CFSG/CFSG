module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.CenterBounds
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFixed
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Placement
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Involutions
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFamily.RootGeometry

/-!
# Native elementary geometry of the conjugate symplectic pair

Both parabolic radicals have rank 3n and paired fixed codimension 5n.
Their intersection is the actual Sylow center. Its root subgroups and other
nontrivial subgroups have codimensions 3n and 4n respectively, giving the
strict F−1 inequality for all central subgroups and their conjugates.
Every elementary subgroup is conjugate into a parabolic radical. Symmetric
shear coordinates then put it into a conjugate of the Sylow center or give
fixed codimension at least 5n. The rank bound 3n completes the strict F−1
inequality for all elementary subgroups, also after restriction through the
genuine commutator inclusion.

Involution displacement has dimension at most 4n, so the same alternative
puts every involution into a conjugate of the center. The resulting geometric
Suzuki types identify both root classes with actual matrix-root conjugates.
The graph automorphism interchanges those types and preserves c₂; their
paired codimensions are 3n and 4n respectively.

The natural fixed spaces, pointwise plane stabilizers, relative indices and
actual transvection-root geometry supply the fixed-space-family argument
in the chapter adapter. All results concern the native full or derived
matrix actions; attaining full-group witnesses are not placed in the binary
derived group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389.
-/
