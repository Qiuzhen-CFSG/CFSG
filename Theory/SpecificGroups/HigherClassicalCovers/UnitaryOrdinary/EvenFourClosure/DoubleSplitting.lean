module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.DoubleSplitting.Assembly

/-!
# Even SU₄ double-cover splitting: local assembly

The determinant-one plane local has odd index, its literal SL₂ Levi lifts
through every finite central cover when the matrix field has at least eight
elements, and an equivariant radical section assembles with that lift. The
assembly produces the requested full-plane section and applies the original
`not_two_kernel_of_plane_section` transfer theorem.

Two radical calculations are still needed for an unconditional result: the
full lifted Hermitian radical must be abelian, and this abelian preimage must
admit an equivariant section. Neither is asserted by this module. The source
application retains n ≥ 2, so q = 2 remains excluded.

Source: Aschbacher–Smith I.1.3–4, printed pp.407–408 of
`refs/quasithin.pdf`, and GLS3 §6.1.
-/
