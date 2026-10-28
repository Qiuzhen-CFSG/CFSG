module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.LocalAmalgam
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Realization
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Actual
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Count

/-!
# The automorphism bound for the binary derived amalgam

The two actual order-96 parabolics and their whole order-32 intersection
have a three-generator signature: one common element and a cubic on each
side. The checked coordinate comparison with the published word tables makes
this signature injective and places it in the finite relator-and-overlap sieve.
The kernel-checked cover by 64 signatures therefore bounds the actual amalgam
automorphisms by 64.

Both premises of the retained conditional assembly are discharged here. This
supplies the local cardinality premise of the global conjugation argument in
`BinaryAutomorphismGroup`, without assuming that an amalgam automorphism extends
to the whole group.

Source: Aschbacher--Smith F.1.12, printed pp.263–264, and Definition F.4.3,
printed p.274. The source G₂ marking and both inclusion squares are retained.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions

theorem card_binaryAmalgamAut_le_of_word_certificate
    (E : BinaryAmalgamBound.ConcreteRealization)
    (hcount : Nat.card BinaryAmalgamBound.Candidate ≤ 64) :
    Nat.card BinaryAmalgamAut ≤ 64 :=
  (BinaryAmalgamBound.card_binaryAmalgamAut_le_candidate E).trans hcount

/-- The actual marked derived amalgam has at most 64 compatible automorphisms. -/
theorem card_binaryAmalgamAut_le : Nat.card BinaryAmalgamAut ≤ 64 :=
  card_binaryAmalgamAut_le_of_word_certificate
    BinaryAmalgamBound.binaryConcreteRealization BinaryAmalgamBound.card_candidate_le

end Atlas.G2.LieAutomorphismExtensions
