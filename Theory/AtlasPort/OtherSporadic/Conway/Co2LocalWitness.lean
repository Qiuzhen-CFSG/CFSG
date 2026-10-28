/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2LocalWitness.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co2Connector
public import Theory.AtlasPort.OtherSporadic.Conway.Co2SignCommutators

/-!
An explicit local witness in the normal closure of shortened Golay signs.
Concrete conjugation formulas identify its local membership and marked-pair image.

Source: Gerald Höhn, `Atlas/Conway/Co2LocalWitness.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

/-- The second retained hexacode basis word, viewed as a Golay word. -/
def co2WitnessCode : golay := golayEquiv (hexBasis 1,0,0)

theorem co2WitnessCode_val : co2WitnessCode.val = jWord (hexGenerators 1) := by
  simp [co2WitnessCode,golayEquiv_apply,hexBasis_coe]

theorem co2WitnessCode_short : co2WitnessCode.val ((0,0),0) = 0 ∧
    co2WitnessCode.val ((0,0),1) = 0 := by
  rw [co2WitnessCode_val]
  decide +kernel

def co2WitnessConjugate : LeechIsometryGroup :=
  zeta * signEmbedding (Multiplicative.ofAdd co2WitnessCode) * zeta⁻¹

theorem co2WitnessConjugate_formula (x : leech) :
    (co2WitnessConjugate.val x).val =
      signChange (hexConjugatedSignWord (hexGenerators 1))
        (integerPermutation (hexSwitch (hexGenerators 1)) x.val) := by
  apply rationalEmbedding_injective
  unfold co2WitnessConjugate
  rw [zeta_inv_eq]
  change rationalEmbedding (zeta.val ((signEmbedding (Multiplicative.ofAdd co2WitnessCode)).val
    (zeta.val x))).val = _
  rw [zeta_agrees]
  change sextetReflection (rationalEmbedding (signChange co2WitnessCode.val (zeta.val x).val)) = _
  rw [rationalEmbedding_signChange,zeta_agrees,co2WitnessCode_val]
  exact sextet_sign_conjugation (hexGenerators 1) x.val

theorem co2Witness_parameters :
    hexConjugatedSignWord (hexGenerators 1) ∈ golay ∧ CodePreserving (hexSwitch (hexGenerators 1)) :=
  signedPermutation_parameters _ _ (fun x => by
    rw [← co2WitnessConjugate_formula]
    exact (co2WitnessConjugate.val x).prop)

/-- Actual Golay automorphism swapping the marked coordinates. -/
def co2PairSwap : Mathieu24CodeModel :=
  ⟨hexSwitch (hexGenerators 1),co2Witness_parameters.2⟩

theorem co2PairSwap_shape : co2PairSwap.val ((0,0),0) = ((0,0),1) ∧
    co2PairSwap.val ((0,0),1) = ((0,0),0) ∧ co2PairSwap * co2PairSwap = 1 := by
  refine ⟨?_,?_,Subtype.ext ?_⟩ <;> decide +kernel

def co2WitnessMonomial : GolayMonomialGroup :=
  ⟨Multiplicative.ofAdd ⟨hexConjugatedSignWord (hexGenerators 1),co2Witness_parameters.1⟩,
    co2PairSwap⟩

theorem co2WitnessMonomial_image :
    monomialEmbedding co2WitnessMonomial = co2WitnessConjugate := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact (co2WitnessConjugate_formula x).symm

def co2NormalWitness : Co2MarkedModel :=
  co2ConnectorElement *
    co2ShortSignElement co2WitnessCode co2WitnessCode_short.1 co2WitnessCode_short.2 *
    co2ConnectorElement⁻¹

theorem co2NormalWitness_formula : co2NormalWitness.val =
    co2ConnectorSign * co2WitnessConjugate * co2ConnectorSign := by
  have hc : co2ConnectorSign * signEmbedding (Multiplicative.ofAdd co2WitnessCode) =
      signEmbedding (Multiplicative.ofAdd co2WitnessCode) * co2ConnectorSign := by
    change signEmbedding (Multiplicative.ofAdd (golayBasis 0)) * signEmbedding _ =
      signEmbedding _ * signEmbedding (Multiplicative.ofAdd (golayBasis 0))
    exact (map_mul signEmbedding _ _).symm.trans
      ((congrArg signEmbedding (mul_comm _ _)).trans (map_mul signEmbedding _ _))
  have hs : co2ConnectorSign⁻¹ = co2ConnectorSign :=
    (inv_eq_iff_mul_eq_one).mpr co2ConnectorSign_sq
  change (co2ConnectorSign*zeta*co2ConnectorSign) * signEmbedding _ *
    (co2ConnectorSign*zeta*co2ConnectorSign)⁻¹ = _
  rw [mul_inv_rev,mul_inv_rev,hs]
  unfold co2WitnessConjugate
  calc
    _ = co2ConnectorSign*zeta*
        (co2ConnectorSign*signEmbedding (Multiplicative.ofAdd co2WitnessCode)*co2ConnectorSign)*
        zeta⁻¹*co2ConnectorSign := by group
    _ = _ := by
      rw [hc,mul_assoc (signEmbedding _) co2ConnectorSign co2ConnectorSign,
        co2ConnectorSign_sq,mul_one]
      group

theorem co2NormalWitness_local : co2NormalWitness ∈
    orthogonalLineStabilizer ((0,0),0) ((0,0),1) := by
  rw [orthogonalLineStabilizer_eq_monomial _ _ (by decide)]
  change co2NormalWitness.val ∈ monomialSubgroup
  rw [co2NormalWitness_formula]
  exact monomialSubgroup.mul_mem
    (monomialSubgroup.mul_mem co2ConnectorSign_monomial
      ⟨co2WitnessMonomial,co2WitnessMonomial_image⟩) co2ConnectorSign_monomial

theorem co2NormalWitness_mem_normal (N : Subgroup Co2MarkedModel) [N.Normal]
    (h : co2ShortSignElement co2WitnessCode co2WitnessCode_short.1 co2WitnessCode_short.2 ∈ N) :
    co2NormalWitness ∈ N :=
  (inferInstance : N.Normal).conj_mem _ h co2ConnectorElement

end Atlas.Conway
