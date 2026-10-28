module

public import Theory.Mathieu.M12.SmallParabolicPair.CoverOrbits.Residual

/-!
# The actual M₁₂ orbit geometry for the central-cover argument

The concrete binary quotient coordinates, five fusion-marked cubic orbits,
and square equation are combined with the two-residual of the marked
involution centralizer. The residual has order 96 and the original
quaternion core as its two-core. The explicit central-class involution
`leftI * rightI * FirstCore.secondSwap` lies outside this residual and,
together with it, generates the full involution centralizer.

This supplies the unconditional model witness consumed by the M₁₂ branch
of the double-cover argument. It makes no assertion about the multiplier
or about outer automorphisms.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair

/-- The five-orbit calculation on the actual Witt-design M₁₂ carrier. -/
noncomputable def coverOrbitData : CoverOrbitData where
  coordinates := CoverOrbits.coordinates
  coordinates_surjective := CoverOrbits.coordinates_surjective
  coordinates_ker := CoverOrbits.coordinates_ker
  left_axis := CoverOrbits.left_axis
  right_axis := CoverOrbits.right_axis
  cubic_equivariance := CoverOrbits.cubic_equivariance
  square_mark := CoverOrbits.square_mark
  orbit_order := CoverOrbits.orbit_order
  central_fusion := CoverOrbits.central_fusion
  noncentral_fusion := CoverOrbits.noncentral_fusion
  residual_core := CoverOrbits.residual_core
  residual_card := CoverOrbits.residual_card
  extra := CoverOrbits.extra
  extra_order := CoverOrbits.extra_order
  extra_mem := CoverOrbits.extra_mem
  extra_not_mem := CoverOrbits.extra_not_mem
  extra_fusion := CoverOrbits.extra_fusion
  centralizer_generated := CoverOrbits.centralizer_generated

end Sporadic.Mathieu.M12SmallPair
