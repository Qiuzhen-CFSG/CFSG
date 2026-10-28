module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.SourceCharts.Coefficients
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.SourceCharts.Weights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds

/-!
# Source extremal chart polynomials and finite cell sums

A covector taking value one on the nonzero top divided-power vector gives
an actual global covariant matrix coefficient. Exact coefficient extraction
and the intrinsic weight-cone bounds prove its chart support and top coefficient.
The proved mixed-grid resonance calculation then gives the nonzero sum on the
literal finite cell. Neither chart, support nor top coefficient is an input.
Both signs and the field of order two are retained.

Source: Steinberg (1963), Sections 8--9; GLS3 Chapter2St2, 13.2(d), 13.3(a).
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.SourceCharts
open DividedPowerEndpoint WeightCone
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The positive highest vector supplies the complete negative-cell chart. -/
theorem exists_negative_chart (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (hcyc : IsCyclicRepresentation rho v)
    (r : K.Point) (hi : InvertsTorus S.torus r)
    (htop : topOperator S rho hr (negativeCoordinateRoot S) n v ≠ 0) :
    ∃ (f : K.PolynomialFunction) (p : MvPolynomial (Fin 12) k),
      RootCovariant S S.roots.positive (S.leftWeightEmbedding (maximalRestrictedWeight n)) f ∧
      (∀ x, f (orderedRootPoint S (negativeCoordinateRoot S) x) = MvPolynomial.eval x p) ∧
      (∀ d ∈ p.support, PolynomialBounds.RootWeightBound (2^n) d) ∧
      p.coeff (PolynomialBounds.rootTopExponent (2^n)) = 1 := by
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one k htop
  obtain ⟨f,p,hf,_,hp,hc⟩ := exists_covariant_chart S rho hr
    S.bigCell.data.positive_witness v _ hv l (negativeCoordinateRoot S)
  refine ⟨f,p,hf,hp,?_,?_⟩
  · intro d hd
    apply negative_word_rootWeightBound S rho hr n v hv hcyc r hi d
    intro hz
    exact (MvPolynomial.mem_support_iff.mp hd) ((hc d).trans (by rw [hz,map_zero]))
  · have h := hc (PolynomialBounds.rootTopExponent (2^n))
    change p.coeff (PolynomialBounds.rootTopExponent (2^n)) =
      l (topOperator S rho hr (negativeCoordinateRoot S) n v) at h
    exact h.trans hl

/-- The opposite highest vector supplies the complete positive-cell chart. -/
theorem exists_positive_chart (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (hcyc : IsCyclicRepresentation rho v)
    (r : K.Point) (hi : InvertsTorus S.torus r)
    (htop : topOperator S rho hr (positiveCoordinateRoot S) n v ≠ 0) :
    ∃ (f : K.PolynomialFunction) (p : MvPolynomial (Fin 12) k),
      RootCovariant S (S.roots.neg ⁻¹' S.roots.positive)
        (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ f ∧
      (∀ x, f (orderedRootPoint S (positiveCoordinateRoot S) x) = MvPolynomial.eval x p) ∧
      (∀ d ∈ p.support, PolynomialBounds.RootWeightBound (2^n) d) ∧
      p.coeff (PolynomialBounds.rootTopExponent (2^n)) = 1 := by
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one k htop
  obtain ⟨f,p,hf,_,hp,hc⟩ := exists_covariant_chart S rho hr
    S.bigCell.data.opposite_witness v _ hv l (positiveCoordinateRoot S)
  refine ⟨f,p,hf,hp,?_,?_⟩
  · intro d hd
    apply positive_word_rootWeightBound S rho hr n v hv hcyc r hi d
    intro hz
    exact (MvPolynomial.mem_support_iff.mp hd) ((hc d).trans (by rw [hz,map_zero]))
  · have h := hc (PolynomialBounds.rootTopExponent (2^n))
    change p.coeff (PolynomialBounds.rootTopExponent (2^n)) =
      l (topOperator S rho hr (positiveCoordinateRoot S) n v) at h
    exact h.trans hl

/-- Literal negative finite-cell interpolation for the original highest module. -/
theorem negative_cell_sum (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (hcyc : IsCyclicRepresentation rho v)
    (r : K.Point) (hi : InvertsTorus S.torus r)
    (htop : topOperator S rho hr (negativeCoordinateRoot S) n v ≠ 0)
    (P : Triality.Standard.Parameters) (C : TwistedCellCoordinates S n P) (hq : P.q = 2^n) :
    HasNonzeroCellSum S n S.roots.positive (S.roots.neg ⁻¹' S.roots.positive)
      (S.leftWeightEmbedding (maximalRestrictedWeight n)) := by
  obtain ⟨f,p,hf,hp,hb,hc⟩ := exists_negative_chart S rho hr n v hv hcyc r hi htop
  apply PolynomialBounds.hasNonzeroCellSum_of_chart_bound S n _ _ _ P
    C.coefficientEmbedding C.negative (negativeCoordinateRoot S) C.negative_point f hf p hp
  · simpa only [hq] using hb
  · rw [hq,hc]
    exact one_ne_zero

/-- Literal positive finite-cell interpolation for the opposite highest module. -/
theorem positive_cell_sum (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (hcyc : IsCyclicRepresentation rho v)
    (r : K.Point) (hi : InvertsTorus S.torus r)
    (htop : topOperator S rho hr (positiveCoordinateRoot S) n v ≠ 0)
    (P : Triality.Standard.Parameters) (C : TwistedCellCoordinates S n P) (hq : P.q = 2^n) :
    HasNonzeroCellSum S n (S.roots.neg ⁻¹' S.roots.positive) S.roots.positive
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ := by
  obtain ⟨f,p,hf,hp,hb,hc⟩ := exists_positive_chart S rho hr n v hv hcyc r hi htop
  apply PolynomialBounds.hasNonzeroCellSum_of_chart_bound S n _ _ _ P
    C.coefficientEmbedding C.positive (positiveCoordinateRoot S) C.positive_point f hf p hp
  · simpa only [hq] using hb
  · rw [hq,hc]
    exact one_ne_zero

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.SourceCharts
