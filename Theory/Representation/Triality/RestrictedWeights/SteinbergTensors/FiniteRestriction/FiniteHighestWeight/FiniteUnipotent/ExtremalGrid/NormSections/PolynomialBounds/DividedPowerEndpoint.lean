module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.Operators

/-!
# Reduction of both D4 divided-power endpoints to intrinsic module facts

An actual ambient inverter transports each torus weight space to the inverse
weight space. The operator calculus places the negative top word in the inverse
highest weight, and the positive top word in the original weight for the
opposite Borel. If the highest weight space is the supplied line, these words
are scalar multiples of the actual inverter translate. Nonvanishing of the
word makes the scalar nonzero.

The highest-line and top-nonvanishing assumptions below remain explicit proof
obligations for cyclic rational highest-weight modules. These reductions do not
assert the unconditional extremal endpoint or any finite restriction theorem.

Source: Steinberg, *Representations of algebraic groups* (1963), Sections 2.8,
4.3 and 8.3; `refs/KGroup/GLS3/Chapter2St2.tex`, 13.2(d), 13.3(a).
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [IsAlgClosed k] in
/-- The inverse of an actual torus inverter also inverts the same torus. -/
theorem inverse_inverts_torus (S : Geometry K) (r : Variety.Point K)
    (hinv : ∀ t : Variety.Point S.torus.carrierVariety,
      r * S.torus.includePoint t * r⁻¹ = (S.torus.includePoint t)⁻¹) :
    ∀ t : Variety.Point S.torus.carrierVariety,
      r⁻¹ * S.torus.includePoint t * (r⁻¹)⁻¹ = (S.torus.includePoint t)⁻¹ := by
  intro t
  have hi := hinv t⁻¹
  change r * S.torus.inclusion.onPoints t⁻¹ * r⁻¹ = (S.torus.inclusion.onPoints t⁻¹)⁻¹ at hi
  rw [map_inv, inv_inv] at hi
  rw [inv_inv]
  change r⁻¹ * S.torus.inclusion.onPoints t * r = (S.torus.inclusion.onPoints t)⁻¹
  calc
    _ = r⁻¹ * (r * (S.torus.inclusion.onPoints t)⁻¹ * r⁻¹) * r :=
      congrArg (fun x => r⁻¹ * x * r) hi.symm
    _ = _ := by group

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- Transport along the actual ambient element, without any root-transport premise. -/
theorem inverter_mem_inverse_weightSpace (S : Geometry K)
    (rho : RationalRepresentation K V) (r : Variety.Point K)
    (hinv : ∀ t : Variety.Point S.torus.carrierVariety,
      r * S.torus.includePoint t * r⁻¹ = (S.torus.includePoint t)⁻¹)
    {mu : TorusWeight S.torus} {v : V} (hv : v ∈ weightSpace rho S.torus mu) :
    (rho.action r).val v ∈ weightSpace rho S.torus mu⁻¹ := by
  intro t
  have htr : S.torus.includePoint t * r = r * S.torus.includePoint t⁻¹ := by
    have hi := hinv t⁻¹
    change r * S.torus.inclusion.onPoints t⁻¹ * r⁻¹ = (S.torus.inclusion.onPoints t⁻¹)⁻¹ at hi
    rw [map_inv, inv_inv] at hi
    change S.torus.inclusion.onPoints t * r = r * S.torus.inclusion.onPoints t⁻¹
    rw [map_inv]
    calc
      _ = (r * (S.torus.inclusion.onPoints t)⁻¹ * r⁻¹) * r :=
        congrArg (fun x => x * r) hi.symm
      _ = _ := by group
  have h := congrArg (fun g => (rho.action g).val v) htr
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h
  rw [hv t⁻¹, map_smul] at h
  have hc : mu.pointCharacter t⁻¹ = (mu⁻¹).pointCharacter t := by
    change (dPointEquiv 1 (mu.onPoints t⁻¹) 0 : k) = _
    rw [map_inv]
    rfl
  rwa [hc] at h

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- A one-dimensional highest weight space determines the inverse extremal line. -/
theorem exists_smul_inverter_of_highestLine (S : Geometry K)
    (rho : RationalRepresentation K V) (r : Variety.Point K)
    (hinv : ∀ t : Variety.Point S.torus.carrierVariety,
      r * S.torus.includePoint t * r⁻¹ = (S.torus.includePoint t)⁻¹)
    (mu : TorusWeight S.torus) (v : V)
    (hline : weightSpace rho S.torus mu = Submodule.span k {v})
    {w : V} (hw : w ∈ weightSpace rho S.torus mu⁻¹) :
    ∃ c : k, w = c • (rho.action r).val v := by
  have hw' := inverter_mem_inverse_weightSpace S rho r⁻¹ (inverse_inverts_torus S r hinv) hw
  rw [inv_inv, hline] at hw'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw'
  refine ⟨c, ?_⟩
  have he := congrArg (fun z => (rho.action r).val z) hc
  rw [map_smul] at he
  have hcancel : (rho.action r).val ((rho.action r⁻¹).val w) = w := by
    calc
      _ = (rho.action (r * r⁻¹)).val w := by rw [map_mul]; rfl
      _ = w := by rw [mul_inv_cancel, map_one]; rfl
  rw [hcancel] at he
  exact he.symm

/-- Conditional endpoint for the positive Borel and negative-root word. -/
theorem negative_endpoint_of_highestLine_of_top_ne_zero (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (r : Variety.Point K)
    (hinv : ∀ t : Variety.Point S.torus.carrierVariety,
      r * S.torus.includePoint t * r⁻¹ = (S.torus.includePoint t)⁻¹)
    (hline : weightSpace rho S.torus (S.leftWeightEmbedding (maximalRestrictedWeight n)) =
      Submodule.span k {v})
    (hne : topOperator S rho hr (negativeCoordinateRoot S) n v ≠ 0) :
    ∃ c : k, c ≠ 0 ∧
      topOperator S rho hr (negativeCoordinateRoot S) n v = c • (rho.action r).val v := by
  obtain ⟨c, hc⟩ := exists_smul_inverter_of_highestLine S rho r hinv _ v hline
    (negative_top_mem_inverse_weightSpace S rho hr n hv.2.2)
  refine ⟨c, ?_, hc⟩
  intro hzero
  exact hne (by simpa only [hzero, zero_smul] using hc)

/-- Conditional endpoint for the opposite Borel and positive-root word. -/
theorem positive_endpoint_of_highestLine_of_top_ne_zero (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (r : Variety.Point K)
    (hinv : ∀ t : Variety.Point S.torus.carrierVariety,
      r * S.torus.includePoint t * r⁻¹ = (S.torus.includePoint t)⁻¹)
    (hline : weightSpace rho S.torus (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ =
      Submodule.span k {v})
    (hne : topOperator S rho hr (positiveCoordinateRoot S) n v ≠ 0) :
    ∃ c : k, c ≠ 0 ∧
      topOperator S rho hr (positiveCoordinateRoot S) n v = c • (rho.action r).val v := by
  have hw : topOperator S rho hr (positiveCoordinateRoot S) n v ∈
      weightSpace rho S.torus ((S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)⁻¹ := by
    simpa only [inv_inv] using positive_top_mem_weightSpace S rho hr n hv.2.2
  obtain ⟨c, hc⟩ := exists_smul_inverter_of_highestLine S rho r hinv _ v hline hw
  refine ⟨c, ?_, hc⟩
  intro hzero
  exact hne (by simpa only [hzero, zero_smul] using hc)

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
