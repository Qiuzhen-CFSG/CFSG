/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3FusionSetup.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3MathieuOrbits
public import Theory.AtlasPort.OtherSporadic.Conway.NormSixFusionWitness
public import Theory.AtlasPort.OtherSporadic.Conway.SextetSignConjugation
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3FusionSetup.lean`, ATLAS revision
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

def co3FusionTriple : Finset Omega := {((0,0),1),((0,0),2),((0,0),3)}
def co3FusionSignCode : golay := golayBasis 6+golayBasis 7+golayBasis 8+golayBasis 9

theorem co3FusionSignCode_val : co3FusionSignCode.val =
    fun p => if p.1 = (0,0) ∨ p.1 = (2,1) then 0 else 1 := by
  change (golayBasis 6).val+(golayBasis 7).val+(golayBasis 8).val+(golayBasis 9).val = _
  simp only [golayBasis_coe]
  decide +kernel

def co3FusionTargetCode : golay := golayBasis 11+golayBasis 10

def co3FusionTarget : Finset Omega := Finset.univ.filter (fun p =>
  if p.1 = (0,0) then p.2 ≠ 0 else p.2 = 0)

theorem co3FusionTarget_octad : co3FusionTarget ∈ octads := by
  apply (octads_mem _).mpr
  refine ⟨co3FusionTargetCode,?_,?_⟩
  · change hammingNorm ((golayBasis 11).val+(golayBasis 10).val) = 8
    simp only [golayBasis_coe]; decide +kernel
  · change binarySupportEquiv ((golayBasis 11).val+(golayBasis 10).val) = _
    simp only [golayBasis_coe]; decide +kernel

theorem co3Fusion_permutation_exists : ∃ p : Mathieu24CodeModel,
    (∀ a ∈ co3FusionTriple, p.val a = a) ∧
    permuteBlock p.val (distinguishedTrio 0) = co3FusionTarget := by
  exact mathieu24_marked_octad_transitive co3FusionTriple (distinguishedTrio 0) co3FusionTarget
    (by decide +kernel) (distinguishedTrio_octads 0) co3FusionTarget_octad
    (by decide +kernel) (by decide +kernel)

def co3FusionIsometry (p : Mathieu24CodeModel) : LeechIsometryGroup :=
  zeta * signIsometry co3FusionSignCode * permutationEmbedding p * signIsometry co3FusionSignCode * zeta

theorem co3Fusion_normal_form :
    signChange co3FusionSignCode.val (zeta.val (normSixVector ((0,0),0))).val =
      oddProfileBase co3FusionTriple ∅ := by
  rw [normSixFusion_formula,co3FusionSignCode_val]
  decide +kernel

theorem co3Fusion_fixes_normSix (p : Mathieu24CodeModel)
    (hp : ∀ a ∈ co3FusionTriple, p.val a = a) :
    (co3FusionIsometry p).val (normSixVector ((0,0),0)) = normSixVector ((0,0),0) := by
  have hT : permuteBlock p.val co3FusionTriple = co3FusionTriple := by
    change co3FusionTriple.image p.val = co3FusionTriple
    calc
      _ = co3FusionTriple.image id := Finset.image_congr (fun a ha => hp a ha)
      _ = _ := Finset.image_id
  have hm : (signIsometry co3FusionSignCode * permutationEmbedding p * signIsometry co3FusionSignCode).val
      (zeta.val (normSixVector ((0,0),0))) = zeta.val (normSixVector ((0,0),0)) := by
    apply Subtype.ext
    change signChange co3FusionSignCode.val (integerPermutation p.val
      (signChange co3FusionSignCode.val (zeta.val (normSixVector ((0,0),0))).val)) = _
    rw [co3Fusion_normal_form,permutation_odd_profile,hT]
    simp only [permuteBlock,Finset.image_empty]
    rw [← co3Fusion_normal_form,signChange_involutive]
  change zeta.val ((signIsometry co3FusionSignCode * permutationEmbedding p * signIsometry co3FusionSignCode).val
    (zeta.val (normSixVector ((0,0),0)))) = _
  rw [hm]
  exact congrArg (fun g : LeechIsometryGroup => g.val (normSixVector ((0,0),0))) zeta_sq

end Atlas.Conway
