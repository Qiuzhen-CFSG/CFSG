module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.Reflection

/-!
# The positive-square fixed-space exclusion: assembly

The simultaneous monomial reduction supplies a quaternion pair with identical
binary kernels and a commuting positive-square signed Golay isometry. The proved
monomial exclusion transports to the literal U-fixed space, excluding dimension
six under just the long-frame, scalar-centralizer and square-one hypotheses.
Since the placed reflection has binary fixed-space dimension six, its integral
lift must square to negation. This discharges the positive-square premise of
the local A₅ fusion argument without assuming the completed G₂ embedding or
faithfulness of the scalar centralizer.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, with Lemma 47.2, p.261, and the root-four conventions on p.269.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

/-- Application to the original U-fixed space, conditional only on the
explicit signed Golay calculation. -/
theorem positive_fixedSpace_finrank_ne_six_of_monomial
    (hm : MonomialQuaternionExclusion) (L : LongFrame) (h : LeechIsometryGroup)
    (hc : leechCentralProjection h ∈ centralizerI) (hsq : h ^ 2 = 1) :
    Module.finrank Bit
      ↥(fixedSpace ⊓ LinearMap.ker (difference (leechCentralProjection h))) ≠ 6 := by
  obtain ⟨a, b, m, ha2, hb2, hab2, hm2, hca, hcb, he, ho, hd⟩ :=
    exists_monomial_quaternion_frame L h hc hsq
  change Module.finrank Bit ↥(fixedSpace ⊓ binaryFixed h) ≠ 6
  rw [hd]
  exact hm a b m ha2 hb2 hab2 hm2 hca hcb he ho

/-- A square-one integral Leech isometry centralizing the full scalar A₄
projectively cannot fix exactly six binary dimensions in the U-fixed space.
The signed Golay exclusion is discharged by the literal lattice calculation. -/
theorem positive_fixedSpace_finrank_ne_six
    (L : LongFrame) (h : LeechIsometryGroup)
    (hc : leechCentralProjection h ∈ centralizerI) (hsq : h ^ 2 = 1) :
    Module.finrank Bit
      ↥(fixedSpace ⊓ LinearMap.ker (difference (leechCentralProjection h))) ≠ 6 :=
  positive_fixedSpace_finrank_ne_six_of_monomial monomialQuaternionExclusion L h hc hsq

/-- The actual placed-reflection consumer of the finite lattice exclusion. -/
theorem reflection_lift_of_monomial_quaternion {L : LongFrame} (P : A5Placement L)
    (hm : MonomialQuaternionExclusion) :
    ∃ h : LeechIsometryGroup,
      leechCentralProjection h = (P.reflection : LeechCentralQuotient) ∧
        h ^ 2 = negationIsometry :=
  P.reflection_lift_of_positive_exclusion
    (positive_fixedSpace_finrank_ne_six_of_monomial hm L)

/-- The placed reflection has a negative-square integral lift: its computed
six-dimensional fixed space rules out the square-one alternative. -/
theorem reflection_lift_square_negation {L : LongFrame} (P : A5Placement L) :
    ∃ h : LeechIsometryGroup,
      leechCentralProjection h = (P.reflection : LeechCentralQuotient) ∧
        h ^ 2 = negationIsometry :=
  P.reflection_lift_of_positive_exclusion (positive_fixedSpace_finrank_ne_six L)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
