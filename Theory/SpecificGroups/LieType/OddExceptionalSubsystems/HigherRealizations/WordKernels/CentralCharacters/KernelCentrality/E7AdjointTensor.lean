module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.Curves
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.DividedPowers

/-!
# The integral E6 adjoint tensor in E7

Restrict the signed integral E7 adjoint operators to the literal E6
Cartan-plus-root basis. The already proved integral basis inclusion intertwines
both signed curves. Full E7 adjoint covariance therefore restricts to the exact
E6 source curve, and the signed simple values give integral pinning.

This constructs all fields of `IntegralAdjointData e7Family` without any field,
characteristic, group-relation, center, or isomorphism premise. The relative
kernel centrality application remains with the parent `KernelCentrality`.
Source: GLS3 §§1.10–1.12 and 2.6.2, the common integral lattice construction.
-/

@[expose] public section
noncomputable section
open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality
open E7AdjointTensor AdjointBlocks
attribute [local instance] Classical.decEq
local instance rootsInTensorAssembly : Fintype typeE7Roots := Fintype.ofFinite _

/-- The E7 adjoint operators on the literal 78-coordinate E6 basis. -/
def e7IntegralTensor (j : Index) : Matrix Coordinate Coordinate ℤ :=
  integralCoordinateOperator (e7Embedding.indexMap j)

private lemma tensorMap_inclusion (S : Type*) [CommRing S] (x : Index → S) :
    tensorMap integralCoordinateOperator S
        (inclusionOver e7Embedding.indexMap S *ᵥ x) =
      tensorMap e7IntegralTensor S x := by
  simp only [tensorMap_apply, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [e7IntegralTensor, inclusionOver_apply, ite_mul]

private theorem e7IntegralTensor_covariance_ring (S : Type*) [CommRing S]
    (a : Bool × Fin 6) (t : S) (j : Index) :
    e7Family.curve a t * (e7IntegralTensor j).map (Int.castRingHom S) =
      (∑ k, sourceFamily.curve a t k j •
        (e7IntegralTensor k).map (Int.castRingHom S)) * e7Family.curve a t := by
  let J := inclusionOver e7Embedding.indexMap S
  have hi : e7Family.curve a t * J = J * sourceFamily.curve a t := by
    simpa only [e7Family, sourceFamily, numberedFamily, IntegralCubicFamily.curve,
      IntegralCubicFamily.coefficient, e7Embedding_base_numbered] using
      e7Embedding.curve_intertwines S a.1 (simpleIndex a.2) t
  have h := numbered_curve_covariance S a t (J *ᵥ Pi.single j 1)
  rw [tensorMap_inclusion, tensorMap_single] at h
  rw [Matrix.mulVec_mulVec, hi, ← Matrix.mulVec_mulVec, tensorMap_inclusion] at h
  simpa only [tensorMap_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h

/-- Basis covariance over the integers with an indeterminate parameter. -/
theorem e7IntegralTensor_covariance (a : Bool × Fin 6) (j : Index) :
    e7Family.curve a (Polynomial.X : Polynomial ℤ) *
        (e7IntegralTensor j).map (Int.castRingHom (Polynomial ℤ)) =
      (∑ k, sourceFamily.curve a (Polynomial.X : Polynomial ℤ) k j •
        (e7IntegralTensor k).map (Int.castRingHom (Polynomial ℤ))) *
          e7Family.curve a (Polynomial.X : Polynomial ℤ) :=
  e7IntegralTensor_covariance_ring (Polynomial ℤ) a Polynomial.X j

/-- The signed simple-root values contain every first E7 divided power integrally. -/
theorem e7IntegralTensor_pinning (a : Bool × Fin 6) :
    ∃ x : Index → ℤ, ∑ j, x j • e7IntegralTensor j = e7Family.dividedPower a 1 := by
  let := typeE6RootPairing.indexNeg
  let := typeE7RootPairing.indexNeg
  rcases a with ⟨s, i⟩
  let j := simpleIndex i
  let k := baseE7 j
  let ε := simpleOperatorOrientation (b := typeE7RootPairing_base) k
  cases s
  · refine ⟨Pi.single (Sum.inr (-j : typeE6Roots)) (-ε), ?_⟩
    have hm : e7Embedding.indexMap (Sum.inr (-j : typeE6Roots)) =
        Sum.inr (-k : typeE7Roots) := by
      change Sum.inr (e7Embedding.index (-j : typeE6Roots)) = _
      rw [RootPairing.indexNeg_neg, RootPairing.indexNeg_neg,
        e7Embedding.neg_index, e7Embedding.base_root]
      rfl
    simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      e7IntegralTensor, hm, integralCoordinateOperator_neg_simple, smul_smul, neg_mul_neg, ε, simpleOperatorOrientation_sq,
      one_smul]
    simp only [e7Family, numberedFamily, simpleFamily, fDividedPower_one]
    exact congrArg fMatrix (baseE7_numbered i)
  · refine ⟨Pi.single (Sum.inr (j : typeE6Roots)) ε, ?_⟩
    have hm : e7Embedding.indexMap (Sum.inr (j : typeE6Roots)) =
        Sum.inr (k : typeE7Roots) := congrArg Sum.inr (e7Embedding.base_root j)
    simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      e7IntegralTensor, hm, integralCoordinateOperator_simple, smul_smul, ε, simpleOperatorOrientation_sq, one_smul]
    simp only [e7Family, numberedFamily, simpleFamily, eDividedPower_one]
    exact congrArg eMatrix (baseE7_numbered i)

/-- The complete integral tensor required by the E7 relative-kernel consumer. -/
def e7IntegralAdjointData : IntegralAdjointData e7Family where
  tensor := e7IntegralTensor
  covariance := e7IntegralTensor_covariance
  pinning := e7IntegralTensor_pinning

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality
