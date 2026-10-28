module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.SourcePBW.Raising
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.SimpleRootOrbits.ChartTransport

/-!
# Source PBW spanning for the two highest-weight conventions

Signed simple-root coefficients stabilize the lowering-algebra orbit: lowering
coefficients act internally, while raising coefficients are straightened past
lowering words and kill the highest vector at the endpoint. Actual root-pair
relations generate the full coefficient algebra from these simple strings.
The lowering PBW theorem then gives exactly the ordered twelve-root span
required by DimensionBound, at every characteristic-power truncation.

The only extra geometric inputs are the actual root-parameter relations and
simple SL2 charts, each supplied by the concrete source producers. There is
no irreducibility, spanning, representation-degree or classification premise.
Source: Steinberg (1963), sections 2–3 and 13.2(d), with both literal Borels.
-/

open Theory.AlgebraicGroup CoefficientPBW
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
lemma coefficientOrbit_le_sideOrbit (S:Geometry K) (hrel:RootPairParameterRelations S)
    (hcharts:∀i:Fin 4,Nonempty (SimpleRootSL2Chart S i))
    (rho:RationalRepresentation K V) (hr:IsRationalRepresentation rho)
    (negative:Bool) (q:ℕ) {χ:TorusWeight S.torus} {v:V}
    (hv:v∈weightSpace rho S.torus χ)
    (hkill:∀(i:Fin 4) (j:ℕ),j ≠ 0 → rootCoefficient S rho hr (raisingRoot S negative i) j v=0) :
    operatorOrbit (coefficientAlgebra S rho hr q) v ≤ operatorOrbit (sideAlgebra S rho hr negative q) v := by
  let U:=operatorOrbit (sideAlgebra S rho hr negative q) v
  have hlo (i:Fin 4) (j:ℕ) (hj:j<q) (z:V) (hz:z∈U) :
      rootCoefficient S rho hr (turn S negative (S.simpleRoot i).val) j z∈U := by
    obtain ⟨l,hl⟩ := simple_side_mem S negative i
    rw [←hl]
    exact operatorOrbit_stable _ v _ (sideCoefficient_mem S rho hr negative q l j hj) z hz
  have hhi (i:Fin 4) (j:ℕ) (hj:j<q) (z:V) (hz:z∈U) :
      rootCoefficient S rho hr (raisingRoot S negative i) j z∈U := by
    obtain ⟨C⟩ := hcharts i
    exact map_operatorOrbit_mem_of_words (sideCoefficient S rho hr negative q) v U _
      (raising_word_mem S hrel negative i C rho hr q hv (hkill i) j hj) z hz
  have hsigned (i:Fin 4) (s:Bool) (j:ℕ) (hj:j<q) (z:V) (hz:z∈U) :
      rootCoefficient S rho hr (if s then (S.simpleRoot i).val else S.roots.neg (S.simpleRoot i).val) j z∈U := by
    cases negative <;> cases s
    · exact hhi i j hj z hz
    · exact hlo i j hj z hz
    · exact hlo i j hj z hz
    · simpa only [raisingRoot,turn,if_true,S.realized.neg_neg] using hhi i j hj z hz
  have ha (a:Module.End k V) (ha:a∈simpleCoefficientAlgebra S rho hr q) : ∀z∈U,a z∈U := by
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨⟨⟨i,s⟩,j⟩,rfl⟩ := ha
      exact hsigned i s j j.isLt
    | algebraMap c => intro z hz; exact U.smul_mem c hz
    | add a b _ _ ha hb => intro z hz; exact U.add_mem (ha z hz) (hb z hz)
    | mul a b _ _ ha hb => intro z hz; exact ha _ (hb z hz)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  apply ha a.val
  · rw [←coefficientAlgebra_eq_simpleCoefficientAlgebra_of_parameterRelations S hrel rho hr q]
    exact a.property
  · exact mem_operatorOrbit _ v

lemma positive_triangular_spanning (S:Geometry K) (hrel:RootPairParameterRelations S)
    (hcharts:∀i:Fin 4,Nonempty (SimpleRootSL2Chart S i))
    (rho:RationalRepresentation K V) (hr:IsRationalRepresentation rho)
    (n:ℕ) {χ:TorusWeight S.torus} {v:V}
    (hv:HasHighWeight rho S.bigCell.data.B S.torus v χ) :
    operatorOrbit (coefficientAlgebra S rho hr (2^n)) v ≤
      orderedCoefficientSpan S rho hr (negativeCoordinateRoot S) (2^n) v := by
  apply (coefficientOrbit_le_sideOrbit S hrel hcharts rho hr true (2^n) hv.2.2 ?_).trans
    (sideOrbit_le_ordered S hrel rho hr true n v)
  intro i j hj
  change rootCoefficient S rho hr (S.roots.neg (S.roots.neg (S.simpleRoot i).val)) j v=0
  rw [S.realized.neg_neg]
  exact rootCoefficient_eq_zero_of_positive_highest S rho hr v hv
    (S.simpleRoot i).val (simple_positive S i) j hj
lemma opposite_triangular_spanning (S:Geometry K) (hrel:RootPairParameterRelations S)
    (hcharts:∀i:Fin 4,Nonempty (SimpleRootSL2Chart S i))
    (rho:RationalRepresentation K V) (hr:IsRationalRepresentation rho)
    (n:ℕ) {χ:TorusWeight S.torus} {v:V}
    (hv:HasHighWeight rho S.bigCell.data.Bopp S.torus v χ) :
    operatorOrbit (coefficientAlgebra S rho hr (2^n)) v ≤
      orderedCoefficientSpan S rho hr (positiveCoordinateRoot S) (2^n) v := by
  apply (coefficientOrbit_le_sideOrbit S hrel hcharts rho hr false (2^n) hv.2.2 ?_).trans
    (sideOrbit_le_ordered S hrel rho hr false n v)
  intro i j hj
  exact rootCoefficient_eq_zero_of_negative_highest S rho hr v hv
    (S.roots.neg (S.simpleRoot i).val) (by rw [S.realized.neg_neg];exact simple_positive S i) j hj
end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.SourcePBW
