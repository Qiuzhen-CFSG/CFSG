module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.LocalAmalgam
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.WordAmalgam
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Candidates
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.WordChecks

/-!
# The actual-group comparison required by the binary amalgam certificate

`ConcreteRealization` asks for coordinate bijections with the literal two
parabolics and their whole overlap, preservation of multiplication, both
inclusion squares, and agreement of matrix labels on common elements.
These are finite model-comparison obligations, not an automorphism bound or
an extension assumption. Once they are proved, the word-table theorem embeds
the actual amalgam automorphisms into the finite candidate sieve.

Source application: Aschbacher--Smith F.1.12 and Definition F.4.3, retaining
the inherited G₂ point/line marking. Construction of the comparison is a
separate obligation; this module proves its cardinality consequence.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
open Theory.GroupTheory

abbrev ConcreteRealization := AmalgamRealization leftTable rightTable binaryAmalgam

theorem card_binaryAmalgamAut_le_candidate (E : ConcreteRealization) :
    Nat.card BinaryAmalgamAut ≤ Nat.card Candidate :=
  Nat.card_le_card_of_injective (E.encode left_valid right_valid)
    (E.encode_injective left_valid right_valid
      (RankTwoAmalgam.ofSubgroups_left_injective BinaryLeft binaryOverlap BinaryRight
        inf_le_left inf_le_right))

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
