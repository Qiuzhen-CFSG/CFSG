/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleFusionCoordinates.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleMathieuOrbits
public import Theory.AtlasPort.OtherSporadic.Conway.Co3FusionFixedPoint
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleFusionCoordinates.lean`, ATLAS revision
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

theorem co3Fusion_moves_mark_outside (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    (p.val co3MarkedCoordinate).1 ≠ (0,0) := by
  have hm : p.val co3MarkedCoordinate ∈ co3FusionTarget := by
    rw [← hO]
    exact Finset.mem_image.mpr ⟨_,by decide +kernel,rfl⟩
  intro hc
  have hr : (p.val co3MarkedCoordinate).2 ≠ 0 := by
    simpa [co3FusionTarget,hc] using hm
  have ht : p.val co3MarkedCoordinate ∈ co3FusionTriple := by
    generalize he : p.val co3MarkedCoordinate = z at hc hr ⊢
    obtain ⟨c,k⟩ := z
    change c = (0,0) at hc
    subst c
    fin_cases k <;> simp_all [co3FusionTriple]
  have he : p.val co3MarkedCoordinate = co3MarkedCoordinate := p.val.injective (hp _ ht)
  rw [he] at hm
  change co3MarkedCoordinate ∈ co3FusionTarget at hm
  norm_num [co3FusionTarget,co3MarkedCoordinate] at hm

theorem co3Fusion_triangle_base_input :
    (signIsometry co3FusionSignCode*zeta).val (oddMinimumVector co3MarkedCoordinate 0) =
      oddMinimumVector co3MarkedCoordinate 0 := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (signChange co3FusionSignCode.val
    (zeta.val (oddMinimumVector co3MarkedCoordinate 0)).val) = _
  rw [rationalEmbedding_signChange,zeta_agrees,co3FusionSignCode_val]
  decide +kernel

theorem co3Fusion_triangle_base_coordinate (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    ((co3FusionIsometry p).val (oddMinimumVector co3MarkedCoordinate 0)).val co3MarkedCoordinate = -1 := by
  have hout := co3Fusion_moves_mark_outside p hp hO
  let w : leech := (signIsometry co3FusionSignCode).val
    ((permutationEmbedding p).val (oddMinimumVector co3MarkedCoordinate 0))
  have hw (k : Tetrad) : w.val ((0,0),k) = 1 := by
    change signChange co3FusionSignCode.val
      ((permutationEmbedding p).val (oddMinimumVector co3MarkedCoordinate 0)).val ((0,0),k) = 1
    rw [permutation_oddMinimumVector,map_zero,co3FusionSignCode_val]
    have hi : ((0,0),k) ≠ p.val co3MarkedCoordinate := fun h => hout (congrArg Prod.fst h).symm
    simp [signChange,oddMinimumVector_apply,hi]
  have hz := congrFun (zeta_agrees w) co3MarkedCoordinate
  change ((zeta.val w).val co3MarkedCoordinate : ℚ) =
    sextetReflection (rationalEmbedding w.val) co3MarkedCoordinate at hz
  rw [sextetReflection_apply] at hz
  norm_num [co3MarkedCoordinate,sextetBlockSign,rationalEmbedding,Fin.sum_univ_succ,hw] at hz
  have he : (co3FusionIsometry p).val (oddMinimumVector co3MarkedCoordinate 0) = zeta.val w := by
    change zeta.val ((signIsometry co3FusionSignCode).val ((permutationEmbedding p).val
      ((signIsometry co3FusionSignCode*zeta).val (oddMinimumVector co3MarkedCoordinate 0)))) = _
    rw [co3Fusion_triangle_base_input]
  rw [he]
  exact_mod_cast hz

theorem co3Fusion_triangle_pair_input :
    (signIsometry co3FusionSignCode*zeta).val (minimumPairPlus ((0,0),1) ((0,0),2)) =
      -minimumPairPlus co3MarkedCoordinate ((0,0),3) := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (signChange co3FusionSignCode.val
    (zeta.val (minimumPairPlus ((0,0),1) ((0,0),2))).val) = _
  rw [rationalEmbedding_signChange,zeta_agrees,co3FusionSignCode_val]
  decide +kernel

theorem co3Fusion_triangle_pair_coordinate (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    ((co3FusionIsometry p).val (minimumPairPlus ((0,0),1) ((0,0),2))).val co3MarkedCoordinate = 2 := by
  have hout := co3Fusion_moves_mark_outside p hp hO
  have hp3 : p.val ((0,0),3) = ((0,0),3) := hp _ (by simp [co3FusionTriple])
  let w : leech := (signIsometry co3FusionSignCode).val
    (-minimumPairPlus (p.val co3MarkedCoordinate) ((0,0),3))
  have hw (k : Tetrad) : w.val ((0,0),k) = if k = 3 then -4 else 0 := by
    have hi : ((0,0),k) ≠ p.val co3MarkedCoordinate := fun h => hout (congrArg Prod.fst h).symm
    change signChange co3FusionSignCode.val
      (-minimumPairPlus (p.val co3MarkedCoordinate) ((0,0),3)).val ((0,0),k) = _
    rw [co3FusionSignCode_val]
    simp [signChange,minimumPairPlus,coordinateVector,Pi.single_apply,hi]
    split_ifs <;> norm_num
  have hz := congrFun (zeta_agrees w) co3MarkedCoordinate
  change ((zeta.val w).val co3MarkedCoordinate : ℚ) =
    sextetReflection (rationalEmbedding w.val) co3MarkedCoordinate at hz
  rw [sextetReflection_apply] at hz
  norm_num [co3MarkedCoordinate,sextetBlockSign,rationalEmbedding,Fin.sum_univ_succ,hw] at hz
  have he : (co3FusionIsometry p).val (minimumPairPlus ((0,0),1) ((0,0),2)) = zeta.val w := by
    change zeta.val ((signIsometry co3FusionSignCode).val ((permutationEmbedding p).val
      ((signIsometry co3FusionSignCode*zeta).val (minimumPairPlus ((0,0),1) ((0,0),2))))) = _
    rw [co3Fusion_triangle_pair_input,map_neg,(permutation_minimumPair p _ _).1,hp3]
  rw [he]
  exact_mod_cast hz

end Atlas.Conway
