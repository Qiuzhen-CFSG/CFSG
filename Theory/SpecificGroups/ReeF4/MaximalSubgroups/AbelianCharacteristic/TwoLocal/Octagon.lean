module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.ParabolicComparison
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Setup
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Incidence
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.WeylGroup
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.ApartmentStabilizer

/-!
# The intrinsic Ree octagon and its apartment stabilizers

Both full parabolics are identified with singleton standard parabolics of
the concrete Tits system on the full exceptional fixed group. Its marked
Weyl quotient is dihedral of order sixteen. The resulting coset geometry has
diameter at most eight, girth at least sixteen, and a simple sixteen-cycle.

Every sixteen-cycle is a group translate of the actual normalizer apartment.
The concrete opposite-Borel calculation puts its pointwise fixer in the
fixed torus, which has odd order. Conjugation transports this oddness to
every apartment. All geometric and stabilizer premises are discharged for
`1 ≤ m`; no simplicity or normalizer-coverage hypothesis is used.

Source: GLS3 §§2.3 and 2.6, especially 2.3.2(d) and 2.3.4–5,
`refs/KGroup/GLS3/chapter2.tex`. These are the geometric inputs to the finite
Borel–Tits application in GLS3 Theorem 3.1.3.
-/

public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

/-- The actual full-parabolic coset graph is a generalized octagon: every
pair of vertices is joined by a walk of length at most eight, every simple
cycle has length at least sixteen, and a simple sixteen-cycle exists. -/
theorem octagonGeometry (m : ℕ) (hm : 1 ≤ m) : OctagonGeometry m :=
  octagonGeometry_of_weyl m hm (hasOctagonalWeylGroup m hm)

/-- Every simple sixteen-cycle is a translate of the normalizer apartment
under the original action of the full exceptional fixed group. -/
theorem apartmentTranslates (m : ℕ) (hm : 1 ≤ m) : ApartmentTranslates m :=
  apartmentTranslates_of_weyl m hm (hasOctagonalWeylGroup m hm)

/-- The pointwise stabilizer in the actual Ree group of every simple
sixteen-cycle in its full-parabolic coset graph has odd order. -/
theorem oddApartmentStabilizers (m : ℕ) (hm : 1 ≤ m) : OddApartmentStabilizers m :=
  oddApartmentStabilizers_of_apartment_translates (apartmentTranslates m hm)
    (standardApartment_fixer_odd m hm)

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
