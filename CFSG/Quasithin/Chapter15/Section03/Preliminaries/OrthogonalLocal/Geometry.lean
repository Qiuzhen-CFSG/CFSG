module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.ModelCalculations
public import Theory.GroupTheory.WreathTwoSylowMaximal

/-!
# Natural orthogonal Sylow geometry for Section 15.3

The compatible coordinates identify the source central omega subgroup with
`C_V(T)`, of order two. The literal orthogonal Sylow image is maximal. Each
plane stabilizer has index two in `T`, fixes a four-group in `V`, and has an
elementary abelian image of order four with an actual equivalence to the binary
plane. Its fixed subgroup in either definite plane has order two. Both its
local indices, in the plane normalizer and in the fixed-line centralizer inside
`M`, are odd.

The concrete calculations use the actual matrix wreath action and Sylow
conjugacy. The transport lemmas intertwine that action with ambient conjugation,
so the fixed subgroups and local indices refer to the original groups. This
module discharges all the geometric premises used by the conditional results
`lemma_15_3_2_4_of_sylow_image_maximal`, `lemma_15_3_6_of_local_indices`, and
`lemma_15_3_8_of_plane_facts`. Their other source hypotheses and the remaining
Thompson and Chapter 14 arguments belong to the source assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122, PDF pp.1138–1139. Final source assembly belongs to
`OrthogonalLocal.lean` and `Preliminaries.lean`.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup
namespace NaturalOrthogonalAction
open OrthogonalGeometry

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)

include hTM

/-- The actual Sylow image is maximal in the natural orthogonal actor. -/
theorem image_sylow_isCoatom : IsCoatom (d.image T) :=
  wreath_two_sylow_isCoatom (d.sylowImage T hTM)

include d in
/-- The natural module has a fixed line under the given Sylow subgroup. -/
theorem card_fixedPlane_sylow : Nat.card (fixedPlane V T) = 2 := by
  rw [d.card_fixedPlane hTM]
  exact sylow_fixedVectors_card (d.sylowImage T hTM)

/-- The plane stabilizer fixes a four-group in the natural module. -/
theorem card_fixedPlane_planeStabilizer (i : OrthogonalPlaneIndex) :
    Nat.card (fixedPlane V (planeStabilizer T (d.plane i))) = 4 := by
  rw [d.card_fixedPlane (X := planeStabilizer T (d.plane i)) (inf_le_left.trans hTM),
    d.image_planeStabilizer]
  exact plane_sylow_fixedVectors_card (d.sylowImage T hTM) i

/-- The action image of the plane stabilizer is elementary abelian. -/
theorem elementary_image_planeStabilizer (i : OrthogonalPlaneIndex) :
    IsElementaryAbelian 2 (d.image (planeStabilizer T (d.plane i))) := by
  rw [d.image_planeStabilizer]
  exact plane_sylow_elementary (d.sylowImage T hTM) i

/-- An actual group equivalence identifies the stabilizer image with the binary plane. -/
theorem image_planeStabilizer_mulEquiv (i : OrthogonalPlaneIndex) :
    Nonempty (d.image (planeStabilizer T (d.plane i)) ≃* OrthogonalPlaneVector) := by
  rw [d.image_planeStabilizer]
  exact plane_sylow_mulEquiv (d.sylowImage T hTM) i

/-- In each definite plane the plane stabilizer fixes a line of order two. -/
theorem card_plane_fixed_planeStabilizer (i : OrthogonalPlaneIndex) :
    Nat.card (fixedPlane (d.plane i) (planeStabilizer T (d.plane i))) = 2 := by
  rw [d.card_plane_fixed (X := planeStabilizer T (d.plane i)) (inf_le_left.trans hTM) i,
    d.image_planeStabilizer]
  exact plane_sylow_fixed_line_card (d.sylowImage T hTM) i

/-- The given plane stabilizer is Sylow in its fixed-line centralizer inside `M`. -/
theorem not_dvd_planeStabilizer_centralizer_relIndex (i : OrthogonalPlaneIndex) :
    ¬ 2 ∣ (planeStabilizer T (d.plane i)).relIndex
      (M ⊓ centralizer (fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) : Set G)) := by
  apply d.planeStabilizer_local_centralizer_index T hTM i
  · exact setwise_plane_sylow_relIndex (d.sylowImage T hTM) i
  · exact plane_sylow_fixed_line_pointwise_even_index (d.sylowImage T hTM) i

/-- The source central omega subgroup has order two because it is the Sylow fixed line. -/
theorem card_centralInvolutions
    (d : NaturalOrthogonalAction M (localModule T M)) :
    Nat.card (centralInvolutions T) = 2 := by
  rw [centralInvolutions_eq_fixedPlane T hTM d]
  exact d.card_fixedPlane_sylow T hTM

end NaturalOrthogonalAction
end CFSG.Quasithin.Chapter15.Section03

end
