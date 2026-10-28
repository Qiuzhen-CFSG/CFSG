module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.PointConstruction.PresentationData

/-!
# The remaining concrete Spin relation check

Addition and coroot multiplication are already proved on the Clifford carrier.
Thus the concrete presentation input reduces to the two nonopposite root-pair
commutator formulas. This module makes that reduction explicit without assuming
that an arbitrary source geometry is identified with Spin.

Source: GLS3 Theorem 1.12.1(a,b,d), `refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
namespace SpinComparisonExistence.PointConstruction
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected.Pinning

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The only concrete relation calculations still required: nonopposite
root pairs with and without a root sum. These are identities in actual Spin. -/
structure SpinCommutatorRelations : Prop where
  sum : ∀ r s q : RootIndex, r ≠ s → r ≠ negativeRoot s →
    typeDRootVector 4 q = typeDRootVector 4 r + typeDRootVector 4 s → ∀ a b : k,
    (rootPoint k r a)⁻¹ * (rootPoint k s b)⁻¹ * rootPoint k r a * rootPoint k s b =
      rootPoint k q (a * b)
  noSum : ∀ r s : RootIndex, r ≠ s → r ≠ negativeRoot s →
    (∀ q, typeDRootVector 4 q ≠ typeDRootVector 4 r + typeDRootVector 4 s) →
    ∀ a b : k,
    (rootPoint k r a)⁻¹ * (rootPoint k s b)⁻¹ * rootPoint k r a * rootPoint k s b = 1

/-- Reuse the checked additive and coroot laws; only the root-pair formulas
remain explicit premises. -/
theorem spinEvaluation_kills_relators_of_commutators
    (hc : SpinCommutatorRelations k) :
    ∀ w, Relator k w → spinEvaluation k w = 1 := by
  intro w hw
  cases hw with
  | addition r a b =>
      simp only [map_mul, map_inv, spinEvaluation_x, rootPoint_add, mul_inv_cancel]
  | sum r s q hrs hopp hq a b =>
      simp only [comm, map_mul, map_inv, spinEvaluation_x]
      rw [hc.sum r s q hrs hopp hq a b, mul_inv_cancel]
  | noSum r s hrs hopp hq a b =>
      simp only [comm, map_mul, map_inv, spinEvaluation_x]
      exact hc.noSum r s hrs hopp hq a b
  | torus r t v =>
      simp only [map_mul, map_inv, spinEvaluation_h, corootWord_mul, mul_inv_cancel]

end SpinComparisonExistence.PointConstruction
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
