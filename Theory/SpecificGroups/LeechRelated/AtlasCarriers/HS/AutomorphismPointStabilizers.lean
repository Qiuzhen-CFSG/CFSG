module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex
public import Theory.GroupAction.FixedPointOfSmallIndex

/-!
# Automorphisms preserve the point stabilizers in the HS action

Write H for the stabilizer of zero in the exact ATLAS degree-100 carrier.
The finite certificates in `SmallIndex` prove that every maximal proper
subgroup of H with index at most 100 has index divisible by 11.
Restrict the degree-100 action along an arbitrary
automorphism of HS to obtain an action of H. Orbit counting gives a fixed
point because 11 does not divide 100. Thus the image of H is contained in
a point stabilizer, and equality follows since both subgroups have index 100.

The final theorem discharges the small-index premise for the actual carrier;
no simplicity or perfectness assumption is needed. Combined with
`normalizer_surjective_of_pointStabilizer_map`, it covers every abstract
automorphism by a normalizing permutation. The separate normalizer-index
calculation is still needed for the outer restriction.

Source context: the degree-100 action and outer automorphism entry in GLS3,
Table 5.3m, printed p.274. The outer restriction is used in Aschbacher–Smith,
printed p.510, for HS from the SQTK list on printed p.33.
-/

public section
namespace Sporadic.LeechRelated.HS
open Subgroup MulAction

/-- Every point stabilizer in the published transitive action has index 100. -/
theorem pointStabilizer_index (x : Fin 100) : (stabilizer Carrier x).index = 100 := by
  simpa using index_stabilizer_of_transitive (G := Carrier) (x := x)

/-- A common fixed point for the automorphic image gives equality of stabilizers. -/
theorem pointStabilizer_map_eq_of_fixedPoint (α : MulAut Carrier) (y : Fin 100)
    (hy : ∀ h : pointStabilizer, α h • y = y) :
    pointStabilizer.map α.toMonoidHom = stabilizer Carrier y := by
  have hle : pointStabilizer.map α.toMonoidHom ≤ stabilizer Carrier y := by
    rintro g ⟨h, hh, rfl⟩
    exact hy ⟨h, hh⟩
  have hi : (pointStabilizer.map α.toMonoidHom).index =
      (stabilizer Carrier y).index := by
    rw [Subgroup.index_map_of_bijective α.bijective,
      pointStabilizer_index, pointStabilizer_index]
  apply le_antisymm hle
  apply Subgroup.relIndex_eq_one.mp
  have hm := Subgroup.relIndex_mul_index hle
  rw [hi, pointStabilizer_index] at hm
  omega

/-- The small maximal-subgroup indices in H suffice for all abstract automorphisms. -/
theorem pointStabilizer_map_of_smallMaximalIndex
    (hindex : ∀ K : Subgroup pointStabilizer,
      IsCoatom K → K.index ≤ 100 → 11 ∣ K.index) :
    ∀ α : MulAut Carrier, ∃ y : Fin 100,
      pointStabilizer.map α.toMonoidHom = stabilizer Carrier y := by
  intro α
  let : MulAction pointStabilizer (Fin 100) :=
    MulAction.compHom (Fin 100) (α.toMonoidHom.comp pointStabilizer.subtype)
  obtain ⟨y, hy⟩ := exists_fixedPoint_of_smallMaximalIndex_dvd
    (G := pointStabilizer) (X := Fin 100) (d := 11) (by simpa using hindex) (by simp)
  exact ⟨y, pointStabilizer_map_eq_of_fixedPoint α y hy⟩

/-- Every abstract automorphism sends the zero stabilizer to a point stabilizer
in the exact degree-100 HS action. -/
theorem pointStabilizer_map :
    ∀ α : MulAut Carrier, ∃ y : Fin 100,
      pointStabilizer.map α.toMonoidHom = stabilizer Carrier y :=
  pointStabilizer_map_of_smallMaximalIndex SmallIndex.pointStabilizer_smallMaximalIndex

end Sporadic.LeechRelated.HS
