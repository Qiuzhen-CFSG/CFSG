module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Orbit.Certificates

/-!
# Generation by the concrete ATLAS pair in the icosian quotient

The pair has 315 distinct translates of the actual axis-zero root point.
A certified sixth commutator power is, up to the central negative sign, a
conjugate of its root reflection. Thus the pair subgroup contains that
reflection and all root reflections, which generate the whole sign quotient.

The proof uses the genuine Hermitian lattice action and its two-sign quotient.
Coordinates and root geometry are Gerald Höhn's ATLAS construction (see
LICENSES/ATLAS.txt); the pair is for ATLAS `J2G1-P2`. This supplies the generation
input for the comparison context of Aschbacher, *Sporadic Groups* (1994),
Section 47 and Lemma 49.5.
-/

public section
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators

/-- The fixed projective icosian pair generates the entire two-sign quotient. -/
theorem closure_pair_eq_top :
    Subgroup.closure ({x, y} : Set Atlas.Conway.IcosianProjectiveModel) = ⊤ :=
  OrbitCertificate.top_of_certificate OrbitCertificate.reached_all
    OrbitCertificate.axis_reflection_mem

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
