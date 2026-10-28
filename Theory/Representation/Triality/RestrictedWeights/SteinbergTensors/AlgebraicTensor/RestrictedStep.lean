module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Geometry
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Operations
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.Separation
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity

/-!
# The restricted D4 Frobenius tensor irreducibility step

The first polynomial coefficients of the actual pinned root actions define an
endomorphism algebra of a rational representation. In a tensor with an ordinary
Frobenius pullback, these coefficients act only on the first factor. If they
generate its whole endomorphism algebra, tensor separation and point-surjectivity
of Frobenius prove irreducibility of the specified tensor action.

For an irreducible module of binary highest weight in the source-correct left
coordinates, `RootDensity` proves the required density. Combining these results
proves the restricted-factor tensor step for every binary weight, including
zero, and every rational irreducible second factor, including the trivial line.
Both carrier universes are arbitrary. The generic conditional result remains
available independently of the highest-weight hypothesis. No kernel of the
abstract group of field-valued points is used.

Sources: GLS3, Theorem 2.8.5 and Corollary 2.8.6(a), and [St2, Theorem 13.1],
in `refs/KGroup/GLS3/chapter2.tex` and `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open scoped TensorProduct
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
universe u v w
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Root-operator density implies the required irreducibility step for the
specified tensor action. The source step below supplies density from the
2-restricted left highest weight. -/
theorem tensorPullback_irreducible_of_rootOperatorAlgebra_eq_top
    (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hρ : IsRationalRepresentation ρ) (hσ : IsIrreducibleRepresentation σ)
    (hdensity : rootOperatorAlgebra S ρ hρ = ⊤) :
    IsIrreducibleRepresentation (tensorPullback F.morphism ρ σ) := by
  refine ⟨tensorPullback_rational F.morphism ρ σ hρ hσ.1, ?_⟩
  intro U hU
  apply tensor_submodule_eq_bot_or_top ρ (pullback F.morphism σ)
    (pullback_irreducible F.morphism F.surjective σ hσ).2 U hU
  apply left_stable_of_adjoin_eq_top (rootOperator S ρ hρ) hdensity U
  intro α z hz
  rw [← rootOperator_tensorPullback S F ρ σ hρ hσ.1 α]
  exact curveOperator_mem _ _ (rootMorphism S α) U hU z hz

/-- The restricted-factor Steinberg step: an irreducible rational D4 module
of binary left highest weight tensored with the ordinary Frobenius pullback
of any rational irreducible module is rational irreducible. The zero basic
weight and a trivial second factor are included. -/
theorem tensorPullback_irreducible_of_left_basic_highWeight [CharP k 2]
    (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hρ : IsIrreducibleRepresentation ρ) (hσ : IsIrreducibleRepresentation σ)
    (a : BasicWeight)
    (hv : ∃ v, HasHighWeight ρ S.borel S.torus v
      (S.leftWeightEmbedding (coefficient a))) :
    IsIrreducibleRepresentation (tensorPullback F.morphism ρ σ) :=
  tensorPullback_irreducible_of_rootOperatorAlgebra_eq_top S F ρ σ hρ.1 hσ
    (rootOperatorAlgebra_eq_top_of_left_basic_highWeight S ρ hρ a hv)

/-- The same source step on the literal `Representation.tprod` of the point
actions, with the second action composed with the regular Frobenius. -/
theorem tprod_frobenius_irreducible_of_left_basic_highWeight [CharP k 2]
    (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hρ : IsIrreducibleRepresentation ρ) (hσ : IsIrreducibleRepresentation σ)
    (a : BasicWeight)
    (hv : ∃ v, HasHighWeight ρ S.borel S.torus v
      (S.leftWeightEmbedding (coefficient a))) :
    IsIrreducibleRepresentation (algebraicAction (Representation.tprod
      ((Units.coeHom _).comp ρ.action)
      ((Units.coeHom _).comp (σ.action.comp F.morphism.onPoints)))) :=
  tensorPullback_irreducible_of_left_basic_highWeight S F ρ σ hρ hσ a hv

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
