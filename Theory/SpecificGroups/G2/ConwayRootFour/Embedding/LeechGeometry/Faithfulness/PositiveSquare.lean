module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.Kernel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.Frame
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.MonomialDisplacement
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

/-!
# Positive-square lifts in the restricted Leech kernel

Every positive-square lattice isometry whose central projection centralizes I
and which fixes the actual U-fixed space in Λ/2Λ is a central sign. The long
frame supplies the scalar fixed-space identity through the dimension comparison
in `Frame`, excluding short signed displacements of such an isometry. A U-fixed
cross then conjugates it into the Golay monomial group, where the coordinate
calculation constructs a short signed displacement for every noncentral
involution. Both geometric inputs are discharged in `positive_square_kernel`;
no source centralizer identification is assumed.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and Section 48, p.269. The application is the positive-square premise of
`centralizerFaithful_of_lattice_involutions` in the parent `Faithfulness` module.
-/

public section

open Atlas.Conway Atlas.Codes Atlas.Lattices

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry

/-- The positive-square lift branch from two independent coordinate inputs. -/
theorem positive_square_kernel_of_geometry
    (hw : PositiveSquare.ScalarFixedSpaceWitness)
    (hmono : PositiveSquare.MonomialShortDisplacement)
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (hsq : h ^ 2 = 1) : h = 1 ∨ h = negationIsometry := by
  obtain ⟨X, hX⟩ := exists_fixedCross
  apply PositiveSquare.eq_sign_of_fixed_cross hmono h hsq X
  · apply Subtype.ext
    exact hfix X.val hX
  · exact PositiveSquare.not_shortDisplacement_of_scalar hw h hh hfix

/-- The source long-frame construction and the independent monomial displacement
calculation together discharge the positive-square lift branch. -/
theorem positive_square_kernel_of_longFrame
    (L : LocalGenerators.LongFrame)
    (hmono : PositiveSquare.MonomialShortDisplacement)
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (hsq : h ^ 2 = 1) : h = 1 ∨ h = negationIsometry :=
  positive_square_kernel_of_geometry
    (PositiveSquare.scalarFixedSpaceWitness_of_longFrame L) hmono h hh hfix hsq

/-- The positive-square lift branch of the restricted-action kernel: fixing
the literal U-fixed space and projectively centralizing I forces a lattice
involution to be a central sign. No additional geometric premise remains. -/
theorem positive_square_kernel
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (hsq : h ^ 2 = 1) : h = 1 ∨ h = negationIsometry := by
  obtain ⟨L⟩ := LocalGenerators.nonempty_longFrame
  exact positive_square_kernel_of_longFrame L
    PositiveSquare.monomial_short_displacement h hh hfix hsq

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
