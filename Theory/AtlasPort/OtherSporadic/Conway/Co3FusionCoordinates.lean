/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3FusionCoordinates.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3FusionSetup
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3FusionCoordinates.lean`, ATLAS revision
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

def co3FusionInputCoordinates : IntegerCoordinates := fun p =>
  if p.1 = (0,0) then (if p.2 = 0 then 2 else -2)
  else if p.1 = (0,1) then (if p.2 = 0 then -2 else 2) else 0

theorem co3FusionInput_formula :
    signChange co3FusionSignCode.val
      (zeta.val (minimumPairPlus ((0,0),0) ((0,1),0))).val = co3FusionInputCoordinates := by
  apply rationalEmbedding_injective
  rw [rationalEmbedding_signChange,zeta_agrees,co3FusionSignCode_val]
  decide +kernel

theorem co3FusionInput_outside (i : Omega) (hi : i ∉ distinguishedTrio 0) :
    co3FusionInputCoordinates i = 0 := by
  have hh : ¬ (i.1 = (0,0) ∨ i.1 = (0,1)) := by
    simpa [distinguishedTrio,mem_tetrad] using hi
  simp only [not_or] at hh
  simp [co3FusionInputCoordinates,hh.1,hh.2]

theorem co3Fusion_first_block (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget)
    (k : Tetrad) :
    signChange co3FusionSignCode.val (integerPermutation p.val co3FusionInputCoordinates) ((0,0),k) =
      if k = 0 then 0 else -2 := by
  rw [co3FusionSignCode_val]
  simp only [signChange,LinearMap.coe_mk,AddHom.coe_mk,true_or,ite_true]
  change co3FusionInputCoordinates (p.val.symm ((0,0),k)) = _
  by_cases hk : k = 0
  · subst k
    have ha : ((0,0),0) ∉ co3FusionTarget := by decide +kernel
    have hi : p.val.symm ((0,0),0) ∉ distinguishedTrio 0 := by
      intro hi
      apply ha
      rw [← hO]
      exact Finset.mem_image.mpr ⟨_,hi,p.val.apply_symm_apply _⟩
    simpa using co3FusionInput_outside _ hi
  · have hm : ((0,0),k) ∈ co3FusionTriple := by
      fin_cases k <;> simp_all [co3FusionTriple]
    have he : p.val.symm ((0,0),k) = ((0,0),k) :=
      (Equiv.symm_apply_eq p.val).mpr (hp _ hm).symm
    simp [he,co3FusionInputCoordinates,hk]

theorem co3Fusion_image_marked_coordinate (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a)
    (hO : permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget) :
    ((co3FusionIsometry p).val (minimumPairPlus ((0,0),0) ((0,1),0))).val ((0,0),0) = 3 := by
  let w : leech := (signIsometry co3FusionSignCode * permutationEmbedding p *
    signIsometry co3FusionSignCode * zeta).val (minimumPairPlus ((0,0),0) ((0,1),0))
  have hw (k : Tetrad) : w.val ((0,0),k) = if k = 0 then 0 else -2 := by
    change signChange co3FusionSignCode.val (integerPermutation p.val
      (signChange co3FusionSignCode.val (zeta.val (minimumPairPlus ((0,0),0) ((0,1),0))).val)) _ = _
    rw [co3FusionInput_formula]
    exact co3Fusion_first_block p hp hO k
  have h := congrFun (zeta_agrees w) ((0,0),0)
  change ((zeta.val w).val ((0,0),0) : ℚ) = sextetReflection (rationalEmbedding w.val) ((0,0),0) at h
  rw [sextetReflection_apply] at h
  norm_num [sextetBlockSign,rationalEmbedding,Fin.sum_univ_succ,hw] at h
  change (zeta.val w).val ((0,0),0) = 3
  exact_mod_cast h

end Atlas.Conway
