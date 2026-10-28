module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.Realization
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Extremal
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Existence
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.Cyclic

/-!
# Constructing the two extremal highest-weight covers

Fundamental rational existence gives a nonzero highest vector at `(2^n-1)ρ`.
Its irreducible dual supplies the opposite-Borel vector with the inverse
character. Restrict to their cyclic spans, then apply the maximal-dimension
construction to get universal highest-weight covers with the required bounds.

The fundamental existence and both cyclic dimension bounds are explicit
remaining premises. In particular, this module does not yet assert the
unconditional `exists_leftExtremalHighestWeightCovers`. The construction works
also at n=1 and preserves the corrected left-character convention.

Sources: GLS3 §1.14 and 2.8.1–2.8.2; Steinberg,
`refs/KGroup/GLS3/Chapter2St2.tex`, 13.2(d), citing his 1963 Corollary 8.3.
That corollary's irreducible-module degree alone does not bound all cyclic
modules or establish the universal mapping property.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The two algebraic cyclic-module bounds needed for the extremal construction.
This is a remaining dimension-theoretic obligation, not an existence axiom. -/
@[expose] def LeftExtremalCyclicDimensionBounds (S : Geometry K) (n : ℕ) : Prop :=
  CyclicHighestWeightDimensionBound S S.bigCell.data.B
    (S.leftWeightEmbedding (maximalRestrictedWeight n)) ((2 ^ n) ^ 12) ∧
  CyclicHighestWeightDimensionBound S S.bigCell.data.Bopp
    (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ ((2 ^ n) ^ 12)

/-- Fundamental existence supplies nonzero extremal cyclic modules for both
Borels. The opposite character is established using the genuine dual action. -/
theorem exists_leftExtremalCyclicHighestWeightModules_of_fundamentals
    (S : Geometry K) (n : ℕ) (hfund : LeftFundamentalRationalExistence S) :
    Nonempty (CyclicHighestWeightModule S S.bigCell.data.B
      (S.leftWeightEmbedding (maximalRestrictedWeight n))) ∧
    Nonempty (CyclicHighestWeightModule S S.bigCell.data.Bopp
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) := by
  have hn : ∀ i, 0 ≤ maximalRestrictedWeight n i := by
    intro i
    change 0 ≤ (2 : ℤ) ^ n - 1
    exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  obtain ⟨A, v, hv⟩ := leftRationalFactor_exists_of_nonnegative_of_fundamentals
    S hfund (maximalRestrictedWeight n) hn
  obtain ⟨tau, ht, htr⟩ := rationalRepresentation_dual_exists A.action A.irreducible.1
  obtain ⟨l, hl, _⟩ := exists_opposite_dual_highestWeight S.bigCell S.maximalTorus
    A.action A.irreducible v (S.leftWeightEmbedding (maximalRestrictedWeight n)) hv tau ht htr
  obtain ⟨Cpos, _, _⟩ := exists_cyclicHighestWeightModule A.action A.irreducible.1 v hv
  obtain ⟨Cneg, _, _⟩ := exists_cyclicHighestWeightModule tau htr l hl
  exact ⟨⟨Cpos⟩, ⟨Cneg⟩⟩

/-- Conditional construction of the actual universal covers. Fundamental
existence and both cyclic dimension bounds remain explicit proof obligations.
No finite restriction or interpolation premise is used; the result includes n=1. -/
theorem exists_leftExtremalHighestWeightCovers_of_fundamentals_of_cyclicBounds
    (S : Geometry K) (n : ℕ) (hfund : LeftFundamentalRationalExistence S)
    (hbound : LeftExtremalCyclicDimensionBounds S n) :
    ∃ Cpos : HighestWeightCover S S.bigCell.data.B
        (S.leftWeightEmbedding (maximalRestrictedWeight n)),
      ∃ Cneg : HighestWeightCover S S.bigCell.data.Bopp
        (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹,
        Module.finrank k Cpos.Space ≤ (2 ^ n) ^ 12 ∧
        Module.finrank k Cneg.Space ≤ (2 ^ n) ^ 12 := by
  obtain ⟨hpos, hneg⟩ := exists_leftExtremalCyclicHighestWeightModules_of_fundamentals S n hfund
  obtain ⟨Cpos, hcpos⟩ := exists_highestWeightCover_of_cyclicBound
    S.bigCell.data.positive_witness ((2 ^ n) ^ 12) hbound.1 hpos
  obtain ⟨Cneg, hcneg⟩ := exists_highestWeightCover_of_cyclicBound
    S.bigCell.data.opposite_witness ((2 ^ n) ^ 12) hbound.2 hneg
  exact ⟨Cpos, Cneg, hcpos, hcneg⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
