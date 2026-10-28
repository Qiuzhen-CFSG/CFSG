module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Straightening
/-!
# Straightening in the actual supplied D4 root parameters

The compatible SL₂ chart and the supplied one-parameter root maps differ by
independent nonzero scalars c,d. In degree r their contribution to either
straightening identity is `(c*d)^r`. Transporting every coefficient explicitly
preserves the direct-diagonal integral weight and includes zero eigenvectors.

Source: SL₂ integral divided powers underlying Steinberg,
*Representations of algebraic groups* (1963), §§2–3; scalar parameter comparison
for one-parameter root subgroups (GLS3 1.3.5(a)).
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem rescale_divided_sum (E F : ℕ → Module.End k V) (i j : ℕ)
    (c d : k) (v : V) (b : ℕ → k)
    (h : E i (F j v) = ∑ r ∈ Finset.range (min i j + 1), b r • F (j-r) (E (i-r) v)) :
    (c^i • E i) ((d^j • F j) v) =
      ∑ r ∈ Finset.range (min i j + 1), ((c*d)^r*b r) •
        (d^(j-r) • F (j-r)) ((c^(i-r) • E (i-r)) v) := by
  simp only [LinearMap.smul_apply, map_smul]
  rw [h]
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro r hr
  have hri : r ≤ i := by have := Finset.mem_range.mp hr; omega
  have hrj : r ≤ j := by have := Finset.mem_range.mp hr; omega
  congr 1
  rw [show c^i = c^(i-r)*c^r by rw [← pow_add, Nat.sub_add_cancel hri],
      show d^j = d^(j-r)*d^r by rw [← pow_add, Nat.sub_add_cancel hrj], mul_pow]
  ring

variable [CharP k 2]
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization

/-- Both divided-power identities in the supplied root parameters. The factor
`(c*d)^r` records their genuine independent rescalings from the compatible SL₂
chart; no parameter compatibility is silently assumed. -/
theorem rankOneChart_actual_straightening (S : Geometry K) (a : Fin 4)
    (C : SimpleRootSL2Chart S a) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) :
    ∃ c d : k, c ≠ 0 ∧ d ≠ 0 ∧
      ∀ (m : ℤ) (v : V), rankOneHasWeight (rankOneChartMap C) rho m v → ∀ i j : ℕ,
        (rootCoefficient S rho hr (S.simpleRoot a).val i
          (rootCoefficient S rho hr (S.roots.neg (S.simpleRoot a).val) j v) =
          ∑ r ∈ Finset.range (min i j + 1),
            ((c*d)^r*((Ring.choose (m+(i:ℤ)-(j:ℤ)) r : ℤ) : k)) •
              rootCoefficient S rho hr (S.roots.neg (S.simpleRoot a).val) (j-r)
                (rootCoefficient S rho hr (S.simpleRoot a).val (i-r) v)) ∧
        (rootCoefficient S rho hr (S.roots.neg (S.simpleRoot a).val) j
          (rootCoefficient S rho hr (S.simpleRoot a).val i v) =
          ∑ r ∈ Finset.range (min i j + 1),
            ((c*d)^r*((Ring.choose (-m+(j:ℤ)-(i:ℤ)) r : ℤ) : k)) •
              rootCoefficient S rho hr (S.simpleRoot a).val (i-r)
                (rootCoefficient S rho hr (S.roots.neg (S.simpleRoot a).val) (j-r) v)) := by
  obtain ⟨c, d, hc, hd, hx, hy, hE, hF⟩ := rankOneChart_rescale S a C rho hr
  refine ⟨c, d, hc, hd, ?_⟩
  intro m v hv i j
  constructor
  · simp_rw [hE, hF]
    exact rescale_divided_sum _ _ i j c d v _
      (rankOne_straightening (rankOneChartMap C) rho hr m v hv i j)
  · simp_rw [hE, hF]
    have h := rescale_divided_sum
      (curveCoefficient rho hr ((rankOneChartMap C).comp standardSL2LowerMorphism))
      (curveCoefficient rho hr ((rankOneChartMap C).comp standardSL2UpperMorphism))
      j i d c v (fun r => ((Ring.choose (-m+(j:ℤ)-(i:ℤ)) r : ℤ) : k))
      (by simpa only [min_comm] using rankOne_straightening_reverse (rankOneChartMap C) rho hr m v hv i j)
    simpa only [min_comm, mul_comm d c] using h

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
