module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Unipotent
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions

/-!
# Finite highest vectors from regular-function evaluation

Evaluation injectivity on the two literal finite unipotent cells implies
highest-line detection and spanning of the elementary-group highest orbit.
For detection, pair a finite-fixed vector with an opposite highest functional;
a suitable linear combination with the chosen highest vector has coefficient
zero on the finite positive cell. For spanning, a functional annihilating the
finite highest orbit has coefficient zero on the finite negative cell.

The extremal-cell calculation remains an explicit prerequisite. The theorems
in this module do not assert the unconditional finite restriction theorem.
Source: GLS3, Theorem 2.8.2; Steinberg, `Chapter2St2.tex`, Section 13.3(a).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Finite positive-cell evaluation detects the actual highest line. -/
theorem finiteHighestLine_of_cellInjectivity (S : Geometry K) (n : ℕ)
    (hcell : RestrictedCellInjectivity S n) : FiniteHighestLine S n := by
  intro A a ha v hv w hw
  obtain ⟨tau, htau, htaur⟩ := rationalRepresentation_dual_exists A.action A.irreducible.1
  obtain ⟨l, hl, hlv⟩ := exists_opposite_dual_highestWeight S.bigCell S.maximalTorus
    A.action A.irreducible v (S.coordinateEmbedding a) hv tau htau htaur
  let x := l v • w - l w • v
  have hfix (g : positiveUnipotent S n) :
      (A.restrict (S.inclusion n)).ρ g.val x = x := by
    change (A.action.action (S.inclusion n g.val)).1 (l v • w - l w • v) =
      l v • w - l w • v
    have hwg := hw g
    change (A.action.action (S.inclusion n g.val)).1 w = w at hwg
    rw [map_sub, map_smul, map_smul, hwg,
      highestVector_fixed_positiveRoots S A hv _ g.property]
  obtain ⟨f, hf, hfval⟩ := exists_rootCovariant_matrixCoefficient S tau htaur
    S.bigCell.data.opposite_witness l (S.coordinateEmbedding a)⁻¹ hl (Module.Dual.eval k A.Space x)
  have hfzero : f = 0 := (hcell a ha).2 f hf (by
    intro g hg
    rw [hfval]
    change ((tau.action (S.inclusion n g)).1 l) x = 0
    rw [htau]
    have h := hfix (⟨g, hg⟩⁻¹)
    change (A.action.action (S.inclusion n g⁻¹)).1 x = x at h
    rw [map_inv] at h
    rw [h]
    simp [x, mul_comm])
  have hx : x = 0 := by
    apply matrixCoefficient_separates_irreducible A.action A.irreducible l hl.1.1 x
    intro g
    have hz : f g⁻¹ = 0 := congrArg (fun q : K.PolynomialFunction => q g⁻¹) hfzero
    rw [hfval] at hz
    change ((tau.action g⁻¹).1 l) x = 0 at hz
    rwa [htau, inv_inv] at hz
  apply Submodule.mem_span_singleton.mpr
  refine ⟨l w / l v, ?_⟩
  have heq := congrArg (fun y : A.Space => (l v)⁻¹ • y) (sub_eq_zero.mp hx)
  simpa [smul_smul, hlv, div_eq_mul_inv, mul_comm] using heq.symm

/-- Finite negative-cell evaluation makes the actual elementary highest
orbit span; no finite irreducibility assumption is used. -/
theorem finiteHighestOrbitSpan_of_cellInjectivity (S : Geometry K) (n : ℕ)
    (hcell : RestrictedCellInjectivity S n) : FiniteHighestOrbitSpan S n := by
  intro A a ha v hv
  by_contra hne
  obtain ⟨l, hl, hker⟩ := (Submodule.span k (Set.range
    (fun g => (A.restrict (S.inclusion n)).ρ g v))).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hne)
  obtain ⟨f, hf, hfval⟩ := exists_rootCovariant_matrixCoefficient S A.action A.irreducible.1
    S.bigCell.data.positive_witness v (S.coordinateEmbedding a) hv l
  have hfzero : f = 0 := (hcell a ha).1 f hf (by
    intro g _
    rw [hfval]
    exact hker (Submodule.subset_span ⟨g, rfl⟩))
  apply hv.1.1
  apply matrixCoefficient_separates_irreducible A.action A.irreducible l hl v
  intro g
  have hz : f g = 0 := congrArg (fun q : K.PolynomialFunction => q g) hfzero
  rwa [hfval] at hz

/-- Final representation-theoretic assembly from extremal cell interpolation
and rational dominant highest-weight existence. Both premises must be proved
before this supplies the unconditional finite restriction result. -/
theorem finiteHighestLine_and_orbitSpan_of_extremal_of_existence
    (S : Geometry K) (n : ℕ) (hext : ExtremalCellInjectivity S n)
    (hex : ∀ b : Weight, (∀ i, 0 ≤ b i) →
      ∃ A : RationalFactor K, HasHighestWeight S A b) :
    FiniteHighestLine S n ∧ FiniteHighestOrbitSpan S n := by
  have hcell := restrictedCellInjectivity_of_extremal_of_sections S n hext
    (complementarySections_of_highestWeightExistence S n hex)
  exact ⟨finiteHighestLine_of_cellInjectivity S n hcell,
    finiteHighestOrbitSpan_of_cellInjectivity S n hcell⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
