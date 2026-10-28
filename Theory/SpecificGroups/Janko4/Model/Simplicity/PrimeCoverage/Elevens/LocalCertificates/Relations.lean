module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.Coordinates

/-!
# Matrix certificate contracts for the eleven-local subgroup

The presentation relations describe the nonabelian group of order 11³ in the
normal-form convention of `Coordinates`. The second record specifies the
conjugation action of the two ATLAS normalizer words. These records contain
explicit hypotheses, not assertions about the matrices; a separate arithmetic
certificate must construct them for the words in `Elevens.Words`.

Source of the concrete words: ATLAS J4G1-max7W1, as documented in `Words`.
-/

@[expose] public section
namespace Janko4.Simplicity.Elevens

/-- Relations sufficient for a faithful realization of the coordinate group. -/
structure ElevenRelations {G : Type*} [Group G] (x y z : G) : Prop where
  x_pow : x ^ 11 = 1
  y_pow : y ^ 11 = 1
  z_pow : z ^ 11 = 1
  xz : Commute x z
  yz : Commute y z
  commutator : x⁻¹ * y⁻¹ * x * y = z
  z_ne : z ≠ 1

/-- Six concrete identities specifying the two normalizer actions. -/
structure ElevenNormalizerRelations {G : Type*} [Group G] (u v x y z : G) : Prop where
  ux : u⁻¹ * x * u = y ^ 3 * z
  uy : u⁻¹ * y * u = x ^ 7 * y ^ 10 * z ^ 2
  uz : u⁻¹ * z * u = z
  vx : v⁻¹ * x * v = y
  vy : v⁻¹ * y * v = x ^ 5 * y * z ^ 4
  vz : v⁻¹ * z * v = z ^ 6

end Janko4.Simplicity.Elevens
