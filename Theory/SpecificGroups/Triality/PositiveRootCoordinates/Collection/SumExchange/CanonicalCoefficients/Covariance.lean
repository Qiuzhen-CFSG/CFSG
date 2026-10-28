module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.CanonicalCoefficients.SimpleReflection
/-!
# Covariance of the binary D₄ divided-power coefficients

Every concrete divided-power coefficient intertwines a simple Tits lift with
its reflected-root coefficient. Sparse multiplication reduces the Cartan blocks
to two finite identities on the four simple-coroot coordinates. On the root
block the linear identity follows from linearity of the actual root reflection;
the quadratic identity follows from preservation of opposite roots.

Thus the calculation covers every root and the entire 28-dimensional lattice,
without a route choice or a normal-form assumption. Source: the common-lattice
Chevalley construction in GLS3 §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.IntegralGeckConstruction
open scoped BigOperators
namespace Triality.Standard.PositiveCoordinates.SumExchangeData
noncomputable section
private lemma binaryTits_mul_inl (i k : Fin 4) (M : Matrix Index Index (ZMod 2)) (b : Index) :
    (binaryTits i * M) (.inl k) b =
      ∑ j : Fin 4, binaryTits i (.inl k) (.inl j) * M (.inl j) b := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, binaryTits]

private lemma binaryTits_mul_inr (i : Fin 4) (q : Fin 24)
    (M : Matrix Index Index (ZMod 2)) (b : Index) :
    (binaryTits i * M) (.inr q) b = M (.inr (reflectionTable i q)) b := by
  have he (r : Fin 24) : q = reflectionTable i r ↔ r = reflectionTable i q := by
    constructor <;> intro h
    · rw [h, reflectionTable_involutive i r]
    · rw [h, reflectionTable_involutive i q]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, binaryTits, he]

private lemma mul_binaryTits_inl (i j : Fin 4) (M : Matrix Index Index (ZMod 2)) (a : Index) :
    (M * binaryTits i) a (.inl j) =
      ∑ k : Fin 4, M a (.inl k) * binaryTits i (.inl k) (.inl j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, binaryTits]

private lemma mul_binaryTits_inr (i : Fin 4) (r : Fin 24)
    (M : Matrix Index Index (ZMod 2)) (a : Index) :
    (M * binaryTits i) a (.inr r) = M a (.inr (reflectionTable i r)) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, binaryTits]

private lemma all_root_sum_iff (r s t : Fin 24) :
    (typeDRootPairing 2).root (rootEnumeration r) =
      (typeDRootPairing 2).root (rootEnumeration s) +
      (typeDRootPairing 2).root (rootEnumeration t) ↔
    rootCoords r = rootCoords s + rootCoords t := by
  rw [Subtype.ext_iff, funext_iff, funext_iff]
  simp only [Submodule.coe_add, Pi.add_apply, rootCoords_spec,
    ← Int.cast_add, Int.cast_inj]

private lemma reflection_sum_iff (i : Fin 4) (r a b : Fin 24) :
    rootCoords (reflectionTable i a) = rootCoords r + rootCoords b ↔
      rootCoords a = rootCoords (reflectionTable i r) + rootCoords (reflectionTable i b) := by
  simp only [← all_root_sum_iff, rootEnumeration_reflectionTable,
    RootPairing.root_reflectionPerm]
  constructor <;> intro h
  · have he := congrArg ((typeDRootPairing 2).reflection (typeDSimpleRootIndex 2 i)) h
    simpa only [RootPairing.reflection_same, map_add] using he
  · have he := congrArg ((typeDRootPairing 2).reflection (typeDSimpleRootIndex 2 i)) h
    simpa only [map_add, RootPairing.reflection_same] using he

private lemma reflectionTable_negative (i : Fin 4) (r : Fin 24) :
    reflectionTable i (negativeIndex r) = negativeIndex (reflectionTable i r) := by
  revert i r
  decide +kernel

private lemma reflectionTable_eq_iff (i : Fin 4) (a b : Fin 24) :
    reflectionTable i a = b ↔ a = reflectionTable i b := by
  constructor <;> intro h
  · rw [← h, reflectionTable_involutive i a]
  · rw [h, reflectionTable_involutive i b]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma simpleCoefficients_reflection (i k : Fin 4) (r : Fin 24) :
    (∑ j : Fin 4, binaryTits i (.inl k) (.inl j) * (simpleCoefficients r j : ZMod 2)) =
      (simpleCoefficients (reflectionTable i r) k : ZMod 2) := by
  revert i k r
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma rootPairing_reflection (i j : Fin 4) (r : Fin 24) :
    (rootPairing r j : ZMod 2) =
      ∑ k : Fin 4, (rootPairing (reflectionTable i r) k : ZMod 2) *
        binaryTits i (.inl k) (.inl j) := by
  revert i j r
  decide +kernel

private lemma binaryTits_linear (i : Fin 4) (r : Fin 24) :
    binaryTits i * linearCoefficient r =
      linearCoefficient (reflectionTable i r) * binaryTits i := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rw [binaryTits_mul_inl, mul_binaryTits_inl]
    simp [linearCoefficient]
  · rw [binaryTits_mul_inl, mul_binaryTits_inr]
    simp only [linearCoefficient, ← reflectionTable_negative,
      (reflectionTable_involutive i).injective.eq_iff]
    by_cases h : b = negativeIndex r <;> simp [h, simpleCoefficients_reflection]
  · rw [binaryTits_mul_inr, mul_binaryTits_inl]
    simp only [linearCoefficient, reflectionTable_eq_iff]
    by_cases h : a = reflectionTable i r
    · simp only [h, if_true]
      exact rootPairing_reflection i b r
    · simp [h]
  · rw [binaryTits_mul_inr, mul_binaryTits_inr]
    simp only [linearCoefficient, reflection_sum_iff]

private lemma binaryTits_quadratic (i : Fin 4) (r : Fin 24) :
    binaryTits i * quadraticCoefficient r =
      quadraticCoefficient (reflectionTable i r) * binaryTits i := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rw [binaryTits_mul_inl, mul_binaryTits_inl]
    simp [quadraticCoefficient]
  · rw [binaryTits_mul_inl, mul_binaryTits_inr]
    simp [quadraticCoefficient]
  · rw [binaryTits_mul_inr, mul_binaryTits_inl]
    simp [quadraticCoefficient]
  · rw [binaryTits_mul_inr, mul_binaryTits_inr]
    simp only [quadraticCoefficient, Sum.inr.injEq, reflectionTable_eq_iff,
      ← reflectionTable_negative, reflectionTable_involutive i (negativeIndex r)]

/-- Intertwining for all four coefficients and every root. -/
lemma binaryTits_divided (i : Fin 4) (r : Fin 24) (d : Fin 4) :
    binaryTits i * dividedCoefficient r d =
      dividedCoefficient (reflectionTable i r) d * binaryTits i := by
  fin_cases d
  · simp [dividedCoefficient]
  · exact binaryTits_linear i r
  · exact binaryTits_quadratic i r
  · simp [dividedCoefficient]

end
end Triality.Standard.PositiveCoordinates.SumExchangeData
