module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Weyl
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.FixedWords

/-!
# Marked quaternion conjugations on the split seven-plane

The original coroot product is diagonal on the full Geck lattice. Its weights
are linear forms over ZMod 7. The root permutations of the two displayed Weyl
words carry those weights by the precise quaternion marking, and the twisting
word carries their diagram-Frobenius transform back to the same plane.
This proves actual matrix conjugation and twisted fixedness, not merely an
abstract Weyl action. Source: the binary triality seven-torus construction,
ATLAS printed p.89, with the specified coroot columns and Weyl words.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.BinarySevenPlane
open ConcreteBruhat ConcreteBruhat.MatrixRealization ConcreteBruhat.TorusCoordinates
open Parabolics Parabolics.RankOneMatrices PositiveCoordinates.SumExchangeData
open QuaternionSevenPlane
open scoped BigOperators
noncomputable section
local instance torusLatticeDecidableEq : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "F" => ExtensionField P

def exponents (a : Fin 4 → ZMod 7) : Coordinates P :=
  fun i => unitHom (Multiplicative.ofAdd (a i))
def exponentProduct (a : Fin 4 → ZMod 7) := product P (exponents a)
def weight (a : Fin 4 → ZMod 7) (r : Fin 24) : ZMod 7 :=
  a 0 * (rootPairing r 0 : ZMod 7) + a 2 * (rootPairing r 2 : ZMod 7) +
  a 3 * (rootPairing r 3 : ZMod 7) + a 1 * (rootPairing r 1 : ZMod 7)
def diagonalValue (a : Fin 4 → ZMod 7) : Index → F
  | .inl _ => 1
  | .inr r => (unitHom (Multiplicative.ofAdd (weight a r))).val

private lemma weight_enumeration (i : Fin 4) (r : Fin 24) :
    corootWeight i (latticeEnumeration (.inr r)) = rootPairing r i := by
  change (typeDRootPairing 2).pairingIn ℤ (rootEnumeration r)
    (typeDSimpleRootIndex 2 i) = _
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.algebraMap_pairingIn, ← rootEnumeration_simpleIndex,
    typeDRootPairing_pairing]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simp [rootPairing, Int.cast_mul, mul_comm]

lemma unitHom_coeff (a : ZMod 7) (n : ℤ) :
    (unitHom (Multiplicative.ofAdd (a * (n : ZMod 7)))).val =
      (unitHom (Multiplicative.ofAdd a)).val ^ n := by
  have h := congrArg Units.val (map_zpow unitHom (Multiplicative.ofAdd a) n)
  simpa only [← ofAdd_zsmul, zsmul_eq_mul, mul_comm,
    Units.val_zpow_eq_zpow_val] using h

lemma matrix_exponentProduct (a) : matrix P (exponentProduct a) =
    Matrix.diagonal (diagonalValue a) := by
  ext r s
  change (product P (exponents a)).val.val (latticeEnumeration r) (latticeEnumeration s) = _
  rw [product_val P prime_two]
  simp only [Matrix.diagonal_apply, latticeEnumeration.injective.eq_iff]
  by_cases h : r = s
  · subst s
    simp only [if_true]
    cases r with
    | inl i => simp [corootWeight, latticeEnumeration, diagonalValue]
    | inr r =>
      simp only [weight_enumeration, exponents, diagonalValue, weight,
        ofAdd_add, map_mul, Units.val_mul, unitHom_coeff]
  · simp [h]

lemma word_intertwine (l) (a b : Fin 4 → ZMod 7)
    (h : ∀ r, weight a r = weight b (permWord l r)) :
    word l * exponentProduct a = exponentProduct b * word l := by
  apply matrix_injective P
  simp only [map_mul, matrix_exponentProduct]
  ext r s
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [(realizes_word l).matrix_column]
  cases s with
  | inl j =>
    cases r with
    | inl i => simp [diagonalValue]
    | inr q => simp [corootVector]
  | inr s =>
    dsimp only
    rw [rootAction_rootWord]
    by_cases he : r = Sum.inr (permWord l s)
    · subst r
      simp only [if_true, one_mul, mul_one, diagonalValue]
      rw [h]
    · simp [he]

lemma first_conjugates (z : Plane) :
    firstWord * splitEmbedding (Multiplicative.ofAdd z) * firstWord⁻¹ =
      splitEmbedding (Multiplicative.ofAdd (firstMap z)) := by
  have h : ∀ (z : Plane) (r : Fin 24),
      weight (planeCoordinates z) r =
      weight (planeCoordinates (firstMap z)) (permWord [1,0,2,1,0,3] r) := by
    decide +kernel
  have he := word_intertwine [1,0,2,1,0,3] _ _ (h z)
  exact (congrArg (fun g => g * firstWord⁻¹) he).trans (mul_inv_cancel_right _ _)

lemma second_conjugates (z : Plane) :
    secondWord * splitEmbedding (Multiplicative.ofAdd z) * secondWord⁻¹ =
      splitEmbedding (Multiplicative.ofAdd (secondMap z)) := by
  have h : ∀ (z : Plane) (r : Fin 24),
      weight (planeCoordinates z) r =
      weight (planeCoordinates (secondMap z)) (permWord [1,2,3,1,0,2] r) := by
    decide +kernel
  have he := word_intertwine [1,2,3,1,0,2] _ _ (h z)
  exact (congrArg (fun g => g * secondWord⁻¹) he).trans (mul_inv_cancel_right _ _)

lemma frobenius_unitHom (z : ZMod 7) :
    frobenius P (unitHom (Multiplicative.ofAdd z)) =
    unitHom (Multiplicative.ofAdd (z+z)) := by
  apply Units.ext
  change fieldFrobenius P _ = _
  rw [fieldFrobenius_apply]
  change _ ^ 2 = _
  rw [ofAdd_add, map_mul, Units.val_mul, pow_two]

def exponentTwist (a : Fin 4 → ZMod 7) : Fin 4 → ZMod 7 :=
  fun i => a (typeD4DiagramPermutation.symm i) + a (typeD4DiagramPermutation.symm i)

lemma graphField_exponentProduct (a) : graphFieldAutomorphism P (exponentProduct a) =
    exponentProduct (exponentTwist a) := by
  unfold exponentProduct
  rw [graphField_product P prime_two]
  congr 1
  funext i
  exact frobenius_unitHom _

lemma twist_torus (z : Plane) :
    twistWord * graphFieldAutomorphism P (splitEmbedding (Multiplicative.ofAdd z)) =
      splitEmbedding (Multiplicative.ofAdd z) * twistWord := by
  have h : ∀ (z : Plane) (r : Fin 24),
      weight (exponentTwist (planeCoordinates z)) r =
      weight (planeCoordinates z) (permWord [1,0,2,3,1,0,2,3] r) := by
    decide +kernel
  change twistWord * graphFieldAutomorphism P (exponentProduct (planeCoordinates z)) = _
  rw [graphField_exponentProduct]
  exact word_intertwine _ _ _ (h z)

end
end Triality.Standard.BinarySevenPlane
