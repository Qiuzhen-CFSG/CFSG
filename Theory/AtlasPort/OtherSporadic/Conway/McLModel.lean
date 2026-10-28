/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLModel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Action
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PairStabilizer

/-!
The pointwise stabilizer of the specified 2-2-3 Leech triangle.
Fixing its norm-six vector and one endpoint also fixes the second endpoint;
the unordered endpoint stabilizer is identified inside the same Conway3 model.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLModel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
open scoped Pointwise

def mclEndpoint : leech := minimumPairPlus co3MarkedCoordinate co3BasePoint.val

def mclOtherEndpoint : leech := normSixVector co3MarkedCoordinate - mclEndpoint

theorem mcl_other_endpoint_eq : mclOtherEndpoint = oddMinimumVector co3BasePoint.val 0 := by
  have h := normSix_point_decomposition co3MarkedCoordinate co3BasePoint.val (by decide)
  change minimumPairPlus co3MarkedCoordinate co3BasePoint.val + _ = _ at h
  unfold mclOtherEndpoint mclEndpoint
  rw [← h]; abel

theorem mcl_endpoint_norm : integerDot mclEndpoint.val mclEndpoint.val = 32 :=
  minimumPairPlus_norm _ _ (by decide)

theorem mcl_other_endpoint_norm : integerDot mclOtherEndpoint.val mclOtherEndpoint.val = 32 := by
  rw [mcl_other_endpoint_eq]; exact oddMinimumVector_norm _

theorem mcl_endpoints_ne : mclEndpoint ≠ mclOtherEndpoint := by
  intro h
  have hh := congrArg (fun y : leech => y.val co3MarkedCoordinate) h
  rw [mcl_other_endpoint_eq,oddMinimumVector_zero_apply] at hh
  norm_num [mclEndpoint,minimumPairPlus,coordinateVector,Pi.single_apply,co3MarkedCoordinate,co3BasePoint] at hh

theorem mcl_base_pair : Atlas.Sporadic.Conway3.basePoint.val = {mclEndpoint,mclOtherEndpoint} := rfl

/-- Full pointwise stabilizer of the specified 2-2-3 triangle, inside actual Co3. -/
abbrev McLModel := MulAction.stabilizer Atlas.Sporadic.Conway3.Model mclEndpoint

/-- Full unordered-endpoint stabilizer, before identifying its simple kernel. -/
abbrev McLPairStabilizer := Atlas.Sporadic.Conway3.PointStabilizer

theorem mcl_fixes_other_endpoint (g : McLModel) : g.val.val.val mclOtherEndpoint = mclOtherEndpoint := by
  have hx : g.val.val.val (normSixVector co3MarkedCoordinate) = normSixVector co3MarkedCoordinate := g.val.prop
  have ha : g.val.val.val mclEndpoint = mclEndpoint := g.prop
  simp [mclOtherEndpoint,map_sub,hx,ha]

theorem mcl_pair_stabilizer_eq :
    (MulAction.stabilizer Atlas.Sporadic.Conway3.Model Atlas.Sporadic.Conway3.basePoint) =
      Atlas.GroupTheory.PairStabilizer (G := Atlas.Sporadic.Conway3.Model) mclEndpoint mclOtherEndpoint := by
  ext g
  change g • Atlas.Sporadic.Conway3.basePoint = Atlas.Sporadic.Conway3.basePoint ↔ _
  have he : g • Atlas.Sporadic.Conway3.basePoint = Atlas.Sporadic.Conway3.basePoint ↔
      ({mclEndpoint,mclOtherEndpoint} : Finset leech).image g.val.val =
        {mclEndpoint,mclOtherEndpoint} := ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  rw [he,MulAction.mem_stabilizer_iff]
  change _ ↔ g • ({mclEndpoint,mclOtherEndpoint} : Set leech) = {mclEndpoint,mclOtherEndpoint}
  simp only [Finset.image_insert,Finset.image_singleton,Set.smul_set_insert,Set.smul_set_singleton]
  change ({g.val.val mclEndpoint,g.val.val mclOtherEndpoint} : Finset leech) =
    {mclEndpoint,mclOtherEndpoint} ↔
    ({g.val.val mclEndpoint,g.val.val mclOtherEndpoint} : Set leech) = {mclEndpoint,mclOtherEndpoint}
  constructor
  · intro h
    ext y
    simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff]
      using (Finset.ext_iff.mp h y)
  · intro h
    ext y
    simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff]
      using (Set.ext_iff.mp h y)

end Atlas.Conway
