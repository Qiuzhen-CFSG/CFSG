module

public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank
import all Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# A noncentral cubic in the actual derived group of G₂(2)

The nonabelian order-27 subgroup constructed in `BinaryThreeRank` lies in the
derived group: its relative index in that normal subgroup divides both 27
and the derived subgroup's index two. Restricting the subgroup to the derived
group preserves the explicit noncommuting pair, whose first element has cube
one by `BinaryCore.movingActor_cube`.

The internal import is intentional. This companion reuses the private
Heisenberg coordinates and matrix calculations without changing their owning
module or exposing those implementation types in its public statement.

The root model and calculations use the licensed ATLAS port of Gerald Höhn
and the ATLAS contributors; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. This extension adds the derived-group containment
and intrinsic witness transport.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
E.6.8, printed pp.247–248 (PDF pp.258–259), the invocation of 1.2.1(3).
Ambient component normalization is proved separately by the source consumer.
-/

namespace Atlas.G2.BinaryThreeRank

private theorem image_le_commutator :
    embedding.range ≤ commutator (Model (ZMod 2)) := by
  apply Subgroup.relIndex_eq_one.mp
  have hi : (commutator (Model (ZMod 2))).index = 2 := by
    rw [BinaryParabolicPair.commutator_eq_longRootClosure, BinaryException.index_H]
  exact Nat.eq_one_of_dvd_coprimes (by rw [hi, card_image]; decide)
    ((commutator (Model (ZMod 2))).relIndex_dvd_index_of_normal embedding.range)
    (Subgroup.relIndex_dvd_card _ _)

/-- The actual G₂(2)′ contains a three-subgroup with a noncentral cubic. -/
public theorem exists_noncentral_cubic_three_subgroup :
    ∃ P : Subgroup (commutator (Model (ZMod 2))), IsPGroup 3 P ∧
      ∃ x y : P, x ^ 3 = 1 ∧ x * y ≠ y * x := by
  let P := embedding.range.subgroupOf (commutator (Model (ZMod 2)))
  have hP : IsPGroup 3 P :=
    (IsPGroup.of_card (show Nat.card embedding.range = 3 ^ 3 from card_image)).of_equiv
      (Subgroup.subgroupOfEquivOfLe image_le_commutator).symm
  have hx : x ∈ embedding.range :=
    ⟨⟨1, 0, 0⟩, by change x ^ 1 * y ^ 0 * z ^ 0 = x; simp⟩
  have hy : y ∈ embedding.range :=
    ⟨⟨0, 1, 0⟩, by change x ^ 0 * y ^ 1 * z ^ 0 = y; simp⟩
  let a : P := ⟨⟨x, image_le_commutator hx⟩, hx⟩
  let b : P := ⟨⟨y, image_le_commutator hy⟩, hy⟩
  refine ⟨P, hP, a, b, ?_, ?_⟩
  · exact Subtype.ext (Subtype.ext BinaryCore.movingActor_cube)
  · intro he
    exact x_y_ne (congrArg (fun g : P => ((g : commutator (Model (ZMod 2))) :
      Model (ZMod 2))) he)

end Atlas.G2.BinaryThreeRank
