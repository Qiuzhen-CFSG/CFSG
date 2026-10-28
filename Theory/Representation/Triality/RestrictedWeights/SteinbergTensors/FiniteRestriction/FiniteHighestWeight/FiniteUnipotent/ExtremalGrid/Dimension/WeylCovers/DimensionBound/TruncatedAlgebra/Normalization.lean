module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Transport

/-!
# Normalization of the actual truncated D4 coefficient algebra

The nonopposite exchange laws transport root coefficients within the truncated
algebra. For the two opposite simple roots, the actual SL2 chart supplies the
rank-one transport theorem. Simple-root generation then proves normalization
by every group point. The supplied root laws and charts are genuine earlier
geometric inputs, consumed for the concrete Spin pinning in ConcreteRootRelations.
Source: Steinberg, Representations of algebraic groups, §§2--3.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Actual charts and nonopposite root laws normalize every truncation. -/
theorem coefficientAlgebra_normalizes_of_relations (S : Geometry K)
    (hgen : Submonoid.closure (simpleRootPoints S) = ⊤)
    (hrel : RootPairParameterRelations S)
    (hcharts : ∀ i : Fin 4, Nonempty (SimpleRootSL2Chart S i))
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (q : ℕ) :
    Normalizes rho (coefficientAlgebra S rho hr q) := by
  apply coefficientAlgebra_normalizes_of_simpleRootTransport S rho hr q hgen
  rintro g ⟨⟨i,b,s⟩,rfl⟩ r j
  let C := Classical.choice (hcharts i)
  have hrank (r : S.roots.Root) (h : r = (S.simpleRoot i).val ∨ r = S.roots.neg (S.simpleRoot i).val) :
      rootCoefficient S rho hr r j ∈ rankOneAlgebra S rho hr i q := by
    rcases h with rfl | rfl
    · exact rankOneCurveAlgebra_first rho hr _ _ q j j.isLt
    · exact rankOneCurveAlgebra_second rho hr _ _ q j j.isLt
  have hnn := S.realized.neg_neg (S.simpleRoot i).val
  cases b
  · dsimp only
    by_cases h : r = (S.simpleRoot i).val ∨ r = S.roots.neg (S.simpleRoot i).val
    · obtain ⟨a,ha,he⟩ := rankOneAlgebra_opposite_transport S i C rho hr q s _ (hrank r h)
      exact ⟨a,rankOneAlgebra_le S rho hr i q ha,he⟩
    · have hp : r ≠ (S.simpleRoot i).val := fun e => h (Or.inl e)
      have hm : r ≠ S.roots.neg (S.simpleRoot i).val := fun e => h (Or.inr e)
      exact rootCoefficient_transport_of_parameterRelations S hrel rho hr _ r hm.symm
        (by simpa only [hnn] using hp) s q j j.isLt
  · dsimp only
    by_cases h : r = (S.simpleRoot i).val ∨ r = S.roots.neg (S.simpleRoot i).val
    · obtain ⟨a,ha,he⟩ := rankOneAlgebra_simple_transport S i C rho hr q s _ (hrank r h)
      exact ⟨a,rankOneAlgebra_le S rho hr i q ha,he⟩
    · have hp : r ≠ (S.simpleRoot i).val := fun e => h (Or.inl e)
      have hm : r ≠ S.roots.neg (S.simpleRoot i).val := fun e => h (Or.inr e)
      exact rootCoefficient_transport_of_parameterRelations S hrel rho hr _ r hp.symm hm s q j j.isLt
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
