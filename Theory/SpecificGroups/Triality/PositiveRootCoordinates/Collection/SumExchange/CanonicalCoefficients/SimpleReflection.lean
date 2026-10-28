module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.SimpleCoefficients
/-!
# Simple reflections on the full binary D₄ lattice

The root-coordinate reflection table is identified with the actual D₄ Weyl
reflections. The integral Tits lift reduces to a sparse matrix: its Cartan block
is the simple reflection and its root block permutes all 24 roots. The integral
root-string signs disappear under specialization to `ZMod 2`.

These identities retain the entire Geck lattice and support coefficient transport
along arbitrary Tits words. Source: GLS3 §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`) and the integral Tits action in
`IntegralGeckConstruction`.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open RootPairing.IntegralGeckConstruction
open scoped BigOperators
namespace Triality.Standard.PositiveCoordinates.SumExchangeData
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- The four simple reflections in the root enumeration. -/
def reflectionTable (i : Fin 4) : Fin 24 → Fin 24 :=
  ![![0, 2, 1, 3, 12, 13, 14, 15, 16, 17, 18, 19, 4, 5, 6, 7, 8, 9, 10, 11, 20, 21, 22, 23],
    ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 14, 13, 15, 20, 21, 22, 23, 16, 17, 18, 19],
    ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 16, 17, 18, 19, 12, 13, 14, 15, 20, 22, 21, 23],
    ![0, 1, 2, 3, 9, 8, 11, 10, 5, 4, 7, 6, 17, 16, 19, 18, 13, 12, 15, 14, 23, 21, 22, 20]] i

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma reflectionTable_coords (i : Fin 4) (r : Fin 24) :
    rootCoords (reflectionTable i r) =
      rootCoords r - rootPairing r i • rootCoords (simpleIndex i) := by
  revert i r
  decide +kernel

private lemma pairing_coords (r : Fin 24) (i : Fin 4) :
    (typeDRootPairing 2).pairing (rootEnumeration r) (typeDSimpleRootIndex 2 i) =
      (rootPairing r i : ℝ) := by
  rw [← rootEnumeration_simpleIndex, typeDRootPairing_pairing]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simp [rootPairing, Int.cast_sum, Int.cast_mul, mul_comm]

lemma rootEnumeration_reflectionTable (i : Fin 4) (r : Fin 24) :
    rootEnumeration (reflectionTable i r) =
      (typeDRootPairing 2).reflectionPerm (typeDSimpleRootIndex 2 i) (rootEnumeration r) := by
  apply (typeDRootPairing 2).root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, pairing_coords,
    ← rootEnumeration_simpleIndex]
  apply Subtype.ext
  ext k
  simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, rootCoords_spec]
  have h := congrFun (reflectionTable_coords i r) k
  exact_mod_cast h

lemma reflectionTable_involutive (i : Fin 4) : Function.Involutive (reflectionTable i) := by
  change ∀ r, reflectionTable i (reflectionTable i r) = r
  revert i
  decide +kernel

/-- The specialized simple Tits lift, including its Cartan action. -/
def binaryTits (i : Fin 4) : Matrix Index Index (ZMod 2)
  | .inl k, .inl j => (if k = j then 1 else 0) -
      if k = i then (|typeDCartanMatrix 2 i j| : ℤ) else 0
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr q, .inr r => if q = reflectionTable i r then 1 else 0

/-- Reduce integral entries modulo two and reindex the entire lattice. -/
def binarySpecialization (M : Matrix LatticeIndex LatticeIndex ℤ) :
    Matrix Index Index (ZMod 2) :=
  Matrix.reindexRingEquiv (ZMod 2) latticeEnumeration.symm (specializeMatrix M)

lemma binarySpecialization_mul (M N : Matrix LatticeIndex LatticeIndex ℤ) :
    binarySpecialization (M * N) = binarySpecialization M * binarySpecialization N := by
  unfold binarySpecialization
  rw [specializeMatrix_mul, map_mul]

lemma binarySpecialization_one : binarySpecialization 1 = 1 := by
  simp [binarySpecialization]

lemma binarySpecialization_apply (M : Matrix LatticeIndex LatticeIndex ℤ) (a b : Index) :
    binarySpecialization M a b = (M (latticeEnumeration a) (latticeEnumeration b) : ZMod 2) := rfl

lemma binarySpecialization_titsLift (i : Fin 4) :
    binarySpecialization (titsLift (typeDRootPairing_baseEquiv 2 i)) = binaryTits i := by
  ext a b
  rw [binarySpecialization_apply]
  rcases b with j | r
  · have h := congrFun (titsLift_mulVec_u (typeDRootPairing_baseEquiv 2 i)
        (typeDRootPairing_baseEquiv 2 j)) (latticeEnumeration a)
    simp only [u, Matrix.mulVec_single_one, Matrix.col_apply] at h
    change ((titsLift _ (latticeEnumeration a) (.inl _) : ℤ) : ZMod 2) = _
    rw [h]
    rcases a with k | q <;>
      simp [binaryTits, latticeEnumeration, Pi.single_apply, typeDRootPairing_base_cartanMatrix]
  · have h := congrFun (titsLift_mulVec_v (typeDRootPairing_baseEquiv 2 i)
        (rootEnumeration r)) (latticeEnumeration a)
    simp only [v, Matrix.mulVec_single_one, Matrix.col_apply,
      typeDRootPairing_baseEquiv_val, ← rootEnumeration_reflectionTable] at h
    change ((titsLift _ (latticeEnumeration a) (.inr _) : ℤ) : ZMod 2) = _
    rw [h]
    rcases a with k | q <;>
      simp [binaryTits, latticeEnumeration, Pi.single_apply, Int.cast_pow]

end
end Triality.Standard.PositiveCoordinates.SumExchangeData
