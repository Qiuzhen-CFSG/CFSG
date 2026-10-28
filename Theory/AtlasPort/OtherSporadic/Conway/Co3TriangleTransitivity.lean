/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleFusion
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleArithmetic
public import Theory.AtlasPort.OtherSporadic.Combinatorics.FiniteFiberPartition
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumVectorStabilizer
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleTransitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Co3BaseTriangleOrbit := MulAction.orbit Co3MarkedModel (co3BaseTriangle co3MarkedCoordinate)

def co3TriangleOrbitTypes : Finset (Fin 8) :=
  fiberLabels (co3TriangleType co3MarkedCoordinate) Co3BaseTriangleOrbit

theorem co3_triangle_orbit_saturated (x : Co3Triangles co3MarkedCoordinate) (hx : x ∈ Co3BaseTriangleOrbit)
    (y : Co3Triangles co3MarkedCoordinate) (ht : co3TriangleType co3MarkedCoordinate x = co3TriangleType co3MarkedCoordinate y) :
    y ∈ Co3BaseTriangleOrbit := by
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨h,hh⟩ := (co3_triangle_mathieu_orbit_iff co3MarkedCoordinate x y).mpr ht
  exact MulAction.mem_orbit_iff.mpr ⟨mathieu23ToNormSixStabilizer co3MarkedCoordinate h*g,
    by rw [mul_smul,hg,hh]⟩

theorem co3_triangle_orbit_type_iff (y : Co3Triangles co3MarkedCoordinate) :
    co3TriangleType co3MarkedCoordinate y ∈ co3TriangleOrbitTypes ↔ y ∈ Co3BaseTriangleOrbit :=
  mem_fiberLabels _ _ co3_triangle_orbit_saturated y

theorem co3_triangle_orbit_card : Nat.card Co3BaseTriangleOrbit =
    ∑ t ∈ co3TriangleOrbitTypes, co3TriangleSize t :=
  saturated_set_card _ co3TriangleSize (co3_triangle_type_card co3MarkedCoordinate)
    _ co3_triangle_orbit_saturated

theorem co3_triangle_orbit_types_zero_three : 0 ∈ co3TriangleOrbitTypes ∧ 3 ∈ co3TriangleOrbitTypes := by
  constructor
  · rw [← co3_base_triangle_type]
    exact (co3_triangle_orbit_type_iff _).mpr (MulAction.mem_orbit_self _)
  · obtain ⟨g,hg,_⟩ := co3_triangle_two_fusions
    rw [← hg]
    exact (co3_triangle_orbit_type_iff _).mpr (MulAction.mem_orbit_iff.mpr ⟨g,rfl⟩)

theorem co3_triangle_orbit_card_dvd_ambient : Nat.card Co3BaseTriangleOrbit ∣ 8315553613086720000 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Co3MarkedModel
    (co3BaseTriangle co3MarkedCoordinate))
  rw [Nat.card_prod] at h
  have hd : Nat.card Co3BaseTriangleOrbit ∣ Nat.card Co3MarkedModel := ⟨_,h.symm⟩
  have hsub := Subgroup.card_subgroup_dvd_card (fullVectorStabilizer (normSixVector co3MarkedCoordinate))
  rw [leechIsometryGroup_order] at hsub
  exact hd.trans hsub

theorem co3TriangleOrbitTypes_eq_univ : co3TriangleOrbitTypes = Finset.univ := by
  have hd : (∑ t ∈ co3TriangleOrbitTypes,co3TriangleSize t) ∣ 8315553613086720000 := by
    rw [← co3_triangle_orbit_card]; exact co3_triangle_orbit_card_dvd_ambient
  rcases co3_triangle_ambient_divisibility co3TriangleOrbitTypes
    co3_triangle_orbit_types_zero_three.1 co3_triangle_orbit_types_zero_three.2 hd with h | h
  · have hpair : co3TrianglePair ∈ Co3BaseTriangleOrbit := by
      apply (co3_triangle_orbit_type_iff _).mp
      rw [co3TrianglePair_type,h]; simp
    obtain ⟨g,_,hg⟩ := co3_triangle_two_fusions
    have himage : g • co3TrianglePair ∈ Co3BaseTriangleOrbit := by
      obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hpair
      exact MulAction.mem_orbit_iff.mpr ⟨g*k,by rw [mul_smul,hk]⟩
    have h5 := (co3_triangle_orbit_type_iff _).mpr himage
    rw [hg,h] at h5
    exact False.elim ((by decide : (5 : Fin 8) ∉ ({0,1,3} : Finset (Fin 8))) h5)
  · exact h

theorem co3_triangle_full_orbit (y : Co3Triangles co3MarkedCoordinate) : y ∈ Co3BaseTriangleOrbit := by
  apply (co3_triangle_orbit_type_iff y).mp
  rw [co3TriangleOrbitTypes_eq_univ]
  exact Finset.mem_univ _

/-- Transitivity from the eight Golay incidence classes, local fusion, and ambient Co0 divisibility. -/
theorem co3_triangles_transitive : MulAction.IsPretransitive Co3MarkedModel (Co3Triangles co3MarkedCoordinate) := by
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (co3_triangle_full_orbit x)
  obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp (co3_triangle_full_orbit y)
  exact ⟨h*g⁻¹,by rw [← hg,mul_smul,inv_smul_smul,hh]⟩

end Atlas.Conway
