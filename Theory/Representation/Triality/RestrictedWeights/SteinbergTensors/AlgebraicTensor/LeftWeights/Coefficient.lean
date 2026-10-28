module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.TwistTransport.Coefficient

/-!
# Coefficient Frobenius for left basic weights

Output coefficient squaring and geometric Frobenius have the same squared
left character. Reuse their proved rational actions, irreducibility transport,
and highest-weight uniqueness to obtain the actual intertwiner.
Source: GLS3 2.8.3--4 and 2.8.8.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable [CharP k 2]
/-- For every basic factor the actual character is the doubled coordinate weight. -/
theorem leftCoefficientFrobenius_basic_highest (S : D4Geometry K)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight)
    (b : Module.Basis (Fin (Module.finrank k (A.factor a).Space)) k (A.factor a).Space) :
    ∃ v, HasHighWeight (coefficientFrobenius (A.factor a).action b) S.borel S.torus v
      (S.leftWeightEmbedding ((2 : ℕ) • coefficient a)) := by
  obtain ⟨v, hv⟩ := A.highest a
  rw [S.leftWeightEmbedding_nsmul]
  exact ⟨_, coefficientFrobenius_hasHighWeight _ b _ _ v _ hv⟩

/-- Coefficient Frobenius and ordinary geometric Frobenius have an actual
linear intertwining equivalence, by the proved highest-weight uniqueness theorem. -/
theorem leftCoefficientFrobenius_equivalent (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight)
    (b : Module.Basis (Fin (Module.finrank k (A.factor a).Space)) k (A.factor a).Space) :
    ∃ e : (A.factor a).Space ≃ₗ[k] (A.factor a).Space,
      Intertwines (coefficientFrobenius (A.factor a).action b)
        (pullback F.morphism (A.factor a).action) e.toLinearMap := by
  obtain ⟨v, hv⟩ := A.highest a
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell S.bigCell S.maximalTorus
    _ _ (coefficientFrobenius_irreducible _ b (A.factor a).irreducible)
    (pullback_irreducible F.morphism F.surjective _ (A.factor a).irreducible)
    _ _ _ (coefficientFrobenius_hasHighWeight _ b _ _ v _ hv)
    (pullback_hasHighWeight_pow _ _ F.morphism 2 F.borel_stable F.torus_formula _ v _ hv)

/-- A bundled intertwiner between coefficient Frobenius and geometric Frobenius.
The coefficients are squared in `b`; the target pulls back along `F.morphism`. -/
def leftCoefficientFrobeniusEquiv (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight)
    (b : Module.Basis (Fin (Module.finrank k (A.factor a).Space)) k (A.factor a).Space) :
    Representation.Equiv
      ((Units.coeHom _).comp (coefficientFrobenius (A.factor a).action b).action)
      ((A.factor a).restrict F.morphism.onPoints).ρ :=
  .mk (leftCoefficientFrobenius_equivalent S F A a b).choose
    (fun g => LinearMap.ext ((leftCoefficientFrobenius_equivalent S F A a b).choose_spec g))

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
