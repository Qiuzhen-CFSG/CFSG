module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws

/-!
# Actual root-pair relations and the signed-simple coefficient algebra

Root sums are anchored in the standard D4 pairing through the geometry's
actual root-index equivalence. The parameter-relation predicate specifies
the geometric input to coefficient extraction; its definition does not prove
existence of those relations. The constant may depend on the root pair and
the chosen parametrizations, but is nonzero and independent of both parameters.

Source: GLS3 1.12.1(b), 1.12.7, and Steinberg (1963), §2.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Addition in the actual D4 root lattice, rather than an unanchored root tag. -/
@[expose] def RootSum (S : Geometry K) (a b c : S.roots.Root) : Prop :=
  (typeDRootPairing 2).root (S.rootIndex c) =
    (typeDRootPairing 2).root (S.rootIndex a) +
      (typeDRootPairing 2).root (S.rootIndex b)

/-- The positive-system parameter laws before proving nonvanishing of the
sum-root constant. This is an intermediate geometric obligation, not a source
theorem: Weyl transport and rank-one charts must still prove nonvanishing. -/
structure PositiveRootPairParameterRelations (S : Geometry K) : Prop where
  commute : ∀ a ∈ S.roots.positive, ∀ b ∈ S.roots.positive, a ≠ b →
    (¬ ∃ c, RootSum S a b c) → ∀ s t : k,
      Commute ((rootCurve S a).onPoints (kPlusPoint s))
        ((rootCurve S b).onPoints (kPlusPoint t))
  exchange : ∀ a ∈ S.roots.positive, ∀ b ∈ S.roots.positive, ∀ c : S.roots.Root,
    RootSum S a b c → ∃ κ : k, ∀ s t : k,
      (rootCurve S a).onPoints (kPlusPoint s) * (rootCurve S b).onPoints (kPlusPoint t) =
        (rootCurve S b).onPoints (kPlusPoint t) *
          (rootCurve S c).onPoints (kPlusPoint (κ * s * t)) *
            (rootCurve S a).onPoints (kPlusPoint s)

/-- The geometric parameter relations still to be established from subgroup
containment, root uniqueness, and rank-one charts. -/
structure RootPairParameterRelations (S : Geometry K) : Prop where
  commute : ∀ a b : S.roots.Root, a ≠ b → b ≠ S.roots.neg a →
    (¬ ∃ c, RootSum S a b c) → ∀ s t : k,
      Commute ((rootCurve S a).onPoints (kPlusPoint s))
        ((rootCurve S b).onPoints (kPlusPoint t))
  exchange : ∀ a b c : S.roots.Root, RootSum S a b c →
    ∃ κ : k, κ ≠ 0 ∧ ∀ s t : k,
      (rootCurve S a).onPoints (kPlusPoint s) * (rootCurve S b).onPoints (kPlusPoint t) =
        (rootCurve S b).onPoints (kPlusPoint t) *
          (rootCurve S c).onPoints (kPlusPoint (κ * s * t)) *
            (rootCurve S a).onPoints (kPlusPoint s)

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Only the coefficients below q on the eight signed simple roots. -/
@[expose] def simpleCoefficientAlgebra (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) : Subalgebra k (Module.End k V) :=
  Algebra.adjoin k (Set.range fun ij : (Fin 4 × Bool) × Fin q =>
    rootCoefficient S rho hr
      (if ij.1.2 then (S.simpleRoot ij.1.1).val else S.roots.neg (S.simpleRoot ij.1.1).val)
      ij.2)

/-- The restricted generating set is contained in the full one. -/
theorem simpleCoefficientAlgebra_le (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) :
    simpleCoefficientAlgebra S rho hr q ≤ coefficientAlgebra S rho hr q := by
  apply Algebra.adjoin_le
  rintro _ ⟨⟨⟨i, e⟩, j⟩, rfl⟩
  exact rootCoefficient_mem S rho hr q _ j j.isLt

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
