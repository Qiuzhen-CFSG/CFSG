/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3FusionFixedPoint.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3ActionTransitivity
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalPairSigns
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3FusionFixedPoint.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

def co3BasePoint : Mathieu23Points co3MarkedCoordinate :=
  ⟨((0,0),1),by change ((0,0),1) ≠ co3MarkedCoordinate; decide⟩

theorem co3Fusion_base_input :
    (signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) =
      -minimumPairPlus ((0,0),2) ((0,0),3) := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (signChange co3FusionSignCode.val
    (zeta.val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)).val) = _
  rw [rationalEmbedding_signChange,zeta_agrees,co3FusionSignCode_val]
  decide +kernel

theorem co3Fusion_fixes_base_endpoint (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a) :
    (co3FusionIsometry p).val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) =
      minimumPairPlus co3MarkedCoordinate co3BasePoint.val := by
  have hm : (permutationEmbedding p).val ((signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)) =
      (signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) := by
    rw [co3Fusion_base_input,map_neg,(permutation_minimumPair p _ _).1,
      hp _ (by simp [co3FusionTriple]),hp _ (by simp [co3FusionTriple])]
  change zeta.val ((signIsometry co3FusionSignCode).val ((permutationEmbedding p).val
    ((signIsometry co3FusionSignCode * zeta).val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)))) = _
  rw [hm]
  have hs : (signIsometry co3FusionSignCode).val ((signIsometry co3FusionSignCode * zeta).val
      (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)) =
      zeta.val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val) := by
    apply Subtype.ext
    exact signChange_involutive _ _
  rw [hs]
  exact congrArg (fun g : LeechIsometryGroup => g.val (minimumPairPlus co3MarkedCoordinate co3BasePoint.val)) zeta_sq

theorem co3Fusion_fixes_base_decomposition (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a) :
    (⟨co3FusionIsometry p,co3Fusion_fixes_normSix p hp⟩ : Co3MarkedModel) •
      co3PointHeptadDecompositionEquiv _ (Sum.inl co3BasePoint) =
      co3PointHeptadDecompositionEquiv _ (Sum.inl co3BasePoint) := by
  apply Subtype.ext
  change ({minimumPairPlus co3MarkedCoordinate co3BasePoint.val,
    normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate co3BasePoint.val} : Finset leech).image
      (co3FusionIsometry p).val = _
  simp [map_sub,co3Fusion_fixes_normSix p hp,co3Fusion_fixes_base_endpoint p hp]
  rfl

end Atlas.Conway
