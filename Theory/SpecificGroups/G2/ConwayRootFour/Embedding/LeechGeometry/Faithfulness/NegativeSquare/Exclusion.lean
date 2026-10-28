module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.NegativeSquare.Geometry
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.MonomialDisplacement
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

/-!
# Excluding negative-square lifts from the fixed-space kernel

The constructed long frame identifies the literal U-fixed binary space with
the fixed space of each nonidentity U-scalar. A proposed negative-square kernel
lift commutes with one such scalar. Their product squares to one and has no
short signed displacement. The checked monomial displacement theorem, applied
after fixing a cross, makes this product a central sign. Its projective image
then puts the proposed kernel element in U ∩ C(I), which is trivial.

`negative_square_kernel` discharges both geometric premises of the reduction
in `Geometry`. It is the negative-square input to
`centralizerFaithful_of_lattice_involutions`, using its literal central
projection, tetrahedral centralizer and U-fixed space. No root-four marking,
G₂ embedding or identification of the centralizer is a premise.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, printed
pp.283–284, especially V = C_(Λ/2Λ)(u), and Section 48, p.269. This is the
lattice-kernel exclusion for that construction, not a separate numbered
assertion in the source. The underlying lattice models are the attributed
ATLAS ports.
-/

public section

open Atlas.Conway Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.NegativeSquare

/-- A lift of an element of the literal tetrahedral centralizer acting
trivially on the U-fixed space cannot square to central negation. -/
theorem negative_square_kernel
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (hsq : h ^ 2 = negationIsometry) : False := by
  obtain ⟨L⟩ := LocalGenerators.nonempty_longFrame
  exact negative_square_kernel_of_longFrame L
    PositiveSquare.monomial_short_displacement h hh hfix hsq

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.NegativeSquare
