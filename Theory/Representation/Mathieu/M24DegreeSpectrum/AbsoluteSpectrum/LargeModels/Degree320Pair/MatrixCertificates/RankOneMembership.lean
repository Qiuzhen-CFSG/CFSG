module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Membership

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.aInverse

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.RankOneMembership.Products.bInverse


/-!
# Certified rank-one membership for both degree-320 matrices

The two literal generated algebras contain the stored complements. Both
complements kill the published column and covector, their pairing is one, and
the complementary sums have certified right inverses. The finite-ring projection
theorem puts the literal outer products in the algebras, with every numerical
and algebra-membership premise discharged.

The density and native-action consumers retain the independent orbit-spanning
and native-marking premises. Source attribution: `Degree320Pair/source/README.md`.
The complementary candidates remain in `MatrixCertificates/source/`.
-/
public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates

open Thompson.BinaryMatrix RankOneChecks

theorem rankOneMembership_of_complements
    (ha : decode 320 RankOneChecks.Data.aS.toArray ∈ generated false)
    (hb : decode 320 RankOneChecks.Data.bS.toArray ∈ generated true) :
    RankOneMembership := by
  intro variant
  cases variant with

  | false =>
    apply rankOne_mem_of_complement false
      (decode 320 RankOneChecks.Data.aS.toArray)
      (decode 320 RankOneChecks.Data.aUi.toArray)
      ha a_column a_covector a_pairing
    rw [← a_outer, aU_add, Products.aInverse.matrix, ident_matrix]

  | true =>
    apply rankOne_mem_of_complement true
      (decode 320 RankOneChecks.Data.bS.toArray)
      (decode 320 RankOneChecks.Data.bUi.toArray)
      hb b_column b_covector b_pairing
    rw [← b_outer, bU_add, Products.bInverse.matrix, ident_matrix]

/-- Concrete density consumer, with precisely the two complement memberships
and the independent orbit-spanning certificate left explicit. -/
theorem generatorDensity_of_complements
    (ha : decode 320 RankOneChecks.Data.aS.toArray ∈ generated false)
    (hb : decode 320 RankOneChecks.Data.bS.toArray ∈ generated true)
    (ho : OrbitSpanning) : GeneratorDensity :=
  generatorDensity_of_rankOne (rankOneMembership_of_complements ha hb) ho

/-- Native consumer of the certified complementary projections. -/
theorem absolute_of_complements
    (ha : decode 320 RankOneChecks.Data.aS.toArray ∈ generated false)
    (hb : decode 320 RankOneChecks.Data.bS.toArray ∈ generated true)
    (ho : OrbitSpanning) (variant : Bool)
    (ρ : Representation (ZMod 2) Sporadic.Mathieu.M24 Space)
    (hρ : Realizes variant ρ) : ρ.IsAbsolutelyIrreducible :=
  absolute_of_rankOne (rankOneMembership_of_complements ha hb) ho variant ρ hρ

/-- Both literal stored outer products belong to their generated algebras. -/
theorem rankOneMembership : RankOneMembership :=
  rankOneMembership_of_complements a_membership b_membership

/-- Only the independent orbit-spanning certificate remains for full density. -/
theorem generatorDensity_of_orbitSpanning (ho : OrbitSpanning) : GeneratorDensity :=
  generatorDensity_of_rankOne rankOneMembership ho

/-- Native absolute irreducibility from the independently marked action and
orbit-spanning certificate, using unconditional rank-one membership. -/
theorem absolute_of_orbitSpanning (ho : OrbitSpanning) (variant : Bool)
    (ρ : Representation (ZMod 2) Sporadic.Mathieu.M24 Space)
    (hρ : Realizes variant ρ) : ρ.IsAbsolutelyIrreducible :=
  absolute_of_rankOne rankOneMembership ho variant ρ hρ

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
