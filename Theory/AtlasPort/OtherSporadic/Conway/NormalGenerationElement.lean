/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormalGenerationElement.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.SextetSignConjugation
public import Theory.AtlasPort.OtherSporadic.Conway.SignedPermutationRecovery

/-!
An explicit conjugated Golay sign used in normal generation.
The sextet-conjugation formula recovers its signed permutation and its nonidentity permutation component.

Source: Gerald Höhn, `Atlas/Conway/NormalGenerationElement.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def normalGenerationCode : golay := golayEquiv (hexBasis 0,0,0)

theorem normalGenerationCode_val : normalGenerationCode.val = jWord (hexGenerators 0) := by
  simp [normalGenerationCode,golayEquiv_apply,hexBasis_coe]

theorem normalGenerationCode_weight : hammingNorm normalGenerationCode.val = 8 := by
  rw [normalGenerationCode_val]
  decide +kernel

theorem normalGenerationCode_blocks :
    (Finset.univ.filter (fun i : HexIndex => hammingNorm (fun k : Tetrad => normalGenerationCode.val (i,k)) = 2)).card = 4 ∧
    (Finset.univ.filter (fun i : HexIndex => hammingNorm (fun k : Tetrad => normalGenerationCode.val (i,k)) = 0)).card = 2 := by
  rw [normalGenerationCode_val]
  decide +kernel

def normalGenerationConjugate : LeechIsometryGroup :=
  zeta * signEmbedding (Multiplicative.ofAdd normalGenerationCode) * zeta⁻¹

theorem zeta_inv_eq : zeta⁻¹ = zeta := (inv_eq_iff_mul_eq_one).mpr zeta_sq

theorem normalGenerationConjugate_formula (x : leech) :
    (normalGenerationConjugate.val x).val =
      signChange (hexConjugatedSignWord (hexGenerators 0))
        (integerPermutation (hexSwitch (hexGenerators 0)) x.val) := by
  apply rationalEmbedding_injective
  unfold normalGenerationConjugate
  rw [zeta_inv_eq]
  change rationalEmbedding (zeta.val ((signEmbedding (Multiplicative.ofAdd normalGenerationCode)).val
    (zeta.val x))).val = _
  rw [zeta_agrees]
  change sextetReflection (rationalEmbedding (signChange normalGenerationCode.val (zeta.val x).val)) = _
  rw [rationalEmbedding_signChange,zeta_agrees,normalGenerationCode_val]
  exact sextet_sign_conjugation (hexGenerators 0) x.val

theorem normalGeneration_parameters :
    hexConjugatedSignWord (hexGenerators 0) ∈ golay ∧ CodePreserving (hexSwitch (hexGenerators 0)) :=
  signedPermutation_parameters _ _ (fun x => by
    rw [← normalGenerationConjugate_formula]
    exact (normalGenerationConjugate.val x).prop)

def normalGenerationMonomial : GolayMonomialGroup :=
  ⟨Multiplicative.ofAdd ⟨hexConjugatedSignWord (hexGenerators 0),normalGeneration_parameters.1⟩,
    ⟨hexSwitch (hexGenerators 0),normalGeneration_parameters.2⟩⟩

theorem normalGenerationMonomial_image :
    monomialEmbedding normalGenerationMonomial = normalGenerationConjugate := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact (normalGenerationConjugate_formula x).symm

theorem normalGenerationConjugate_mem_monomial : normalGenerationConjugate ∈ monomialSubgroup :=
  ⟨normalGenerationMonomial,normalGenerationMonomial_image⟩

theorem normalGenerationMonomial_permutation_ne_one : normalGenerationMonomial.right ≠ 1 := by
  intro he
  have hp : hexSwitch (hexGenerators 0) = 1 := congrArg Subtype.val he
  have hn : hexSwitch (hexGenerators 0) ≠ 1 := by decide +kernel
  exact hn hp

theorem normalGeneration_permutation_shape :
    (hexSwitch (hexGenerators 0)).support.card = 16 ∧
      hexSwitch (hexGenerators 0) * hexSwitch (hexGenerators 0) = 1 := by
  decide +kernel

end Atlas.Conway
