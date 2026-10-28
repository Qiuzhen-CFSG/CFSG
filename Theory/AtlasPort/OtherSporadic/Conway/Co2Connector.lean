/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2Connector.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2Geometry
public import Theory.AtlasPort.OtherSporadic.Conway.NormalGenerationElement

/-!
An explicit connector in the norm-four Leech-vector stabilizer.
The sextet isometry fixes the marked vector, is involutory, and lies outside the monomial subgroup.

Source: Gerald Höhn, `Atlas/Conway/Co2Connector.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

/-- A Golay sign change turning the marked sum into a difference. -/
def co2ConnectorSign : LeechIsometryGroup := signIsometry (golayBasis 0)

theorem co2ConnectorSign_sq : co2ConnectorSign * co2ConnectorSign = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  change signChange (golayBasis 0).val (signChange (golayBasis 0).val x.val) = x.val
  exact signChange_involutive _ _

theorem co2ConnectorSign_pair : co2ConnectorSign.val (minimumPairPlus ((0,0),0) ((0,0),1)) =
    minimumPairMinus ((0,0),0) ((0,0),1) := by
  apply Subtype.ext
  change signChange (golayBasis 0).val (minimumPairPlus ((0,0),0) ((0,0),1)).val = _
  rw [golayBasis_coe]
  decide +kernel

theorem zeta_fixes_marked_difference : zeta.val (minimumPairMinus ((0,0),0) ((0,0),1)) =
    minimumPairMinus ((0,0),0) ((0,0),1) := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  rw [zeta_agrees]
  decide +kernel

/-- An actual nonmonomial involution in the marked norm-four vector stabilizer. -/
def co2Connector : LeechIsometryGroup := co2ConnectorSign * zeta * co2ConnectorSign

theorem co2Connector_fixes : co2Connector.val (minimumPairPlus ((0,0),0) ((0,0),1)) =
    minimumPairPlus ((0,0),0) ((0,0),1) := by
  change co2ConnectorSign.val (zeta.val (co2ConnectorSign.val _)) = _
  rw [co2ConnectorSign_pair,zeta_fixes_marked_difference,← co2ConnectorSign_pair]
  exact congrArg (fun g : LeechIsometryGroup => g.val (minimumPairPlus ((0,0),0) ((0,0),1)))
    co2ConnectorSign_sq

theorem co2Connector_sq : co2Connector * co2Connector = 1 := by
  unfold co2Connector
  calc
    _ = co2ConnectorSign * zeta * (co2ConnectorSign*co2ConnectorSign) * zeta * co2ConnectorSign := by group
    _ = 1 := by rw [co2ConnectorSign_sq,mul_one,mul_assoc co2ConnectorSign zeta zeta,zeta_sq,mul_one,co2ConnectorSign_sq]

theorem co2ConnectorSign_monomial : co2ConnectorSign ∈ monomialSubgroup := by
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd (golayBasis 0)),?_⟩
  exact congrArg (fun f : Multiplicative golay →* LeechIsometryGroup =>
    f (Multiplicative.ofAdd (golayBasis 0))) monomial_inl

theorem co2Connector_not_monomial : co2Connector ∉ monomialSubgroup := by
  intro h
  have hh := monomialSubgroup.mul_mem (monomialSubgroup.mul_mem co2ConnectorSign_monomial h)
    co2ConnectorSign_monomial
  have he : co2ConnectorSign * co2Connector * co2ConnectorSign = zeta := by
    unfold co2Connector
    calc
      _ = (co2ConnectorSign*co2ConnectorSign) * zeta * (co2ConnectorSign*co2ConnectorSign) := by group
      _ = zeta := by rw [co2ConnectorSign_sq,one_mul,mul_one]
  exact zeta_not_monomial (he ▸ hh)

def co2ConnectorElement : Atlas.Sporadic.Conway2.Model := ⟨co2Connector,co2Connector_fixes⟩

end Atlas.Conway
