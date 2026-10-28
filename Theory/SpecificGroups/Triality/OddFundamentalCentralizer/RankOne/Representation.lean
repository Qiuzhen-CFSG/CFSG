module
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Coordinates
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup

/-!
# Integral rank-one action on the D4 Geck lattice

The exceptional six-dimensional block consists of the four Cartan vectors
and the two roots ±α. The absolute Cartan coefficients, including the diagonal
coefficient 2, extend the symmetric-square action to this block over every
commutative ring. Eight natural two-dimensional blocks and six fixed lines
complete the action. The determinant identity proves multiplication; a natural
block proves faithfulness. Reindexing uses the existing integral root strings.

Sources: GLS3 §§2.4 and 2.6, especially Proposition 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`). This is the rank-one input to the odd
triality case of Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.RankOne
open Parabolics.RankOneMatrices

def cartanAbs (i j : Fin 4) : ℤ :=
  if i = j then 2 else if (i = 1 ∧ j ≠ 1) ∨ (i ≠ 1 ∧ j = 1) then 1 else 0

def specialBlock {F : Type*} [CommRing F] (i : Fin 4)
    (A : Matrix (Fin 2) (Fin 2) F) : Matrix SpecialIndex SpecialIndex F
  | .inl k, .inl j => (if k = j then 1 else 0) +
      if k = i then (cartanAbs i j : F) * A 0 1 * A 1 0 else 0
  | .inl k, .inr s => if k = i then A 0 s * A 1 s else 0
  | .inr r, .inl j => (cartanAbs i j : F) * A r 0 * A r 1
  | .inr r, .inr s => A r s ^ 2

variable {F : Type*} [CommRing F]

set_option maxHeartbeats 2000000 in
lemma specialBlock_one (i : Fin 4) : specialBlock i (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext (k | k) (j | j) <;> simp [specialBlock, Matrix.one_apply]
  all_goals aesop

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
lemma specialBlock_mul (i : Fin 4) (A B : SL(2, F)) :
    specialBlock i ((A * B).1) = specialBlock i A.1 * specialBlock i B.1 := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hdiag : cartanAbs i i = 2 := by simp [cartanAbs]
  ext (k | k) (j | j)
  · by_cases hk : k = i
    · subst k
      simp [specialBlock, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fintype.sum_sum_type, add_mul, mul_add, ite_mul, mul_ite,
        Fin.sum_univ_two, Finset.sum_add_distrib, hdiag]
      grind only
    · simp [specialBlock, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fintype.sum_sum_type, add_mul, mul_add, ite_mul, mul_ite,
        Fin.sum_univ_two, Finset.sum_add_distrib, hdiag, hk]
  · by_cases hk : k = i
    · subst k
      fin_cases j <;>
        simp [specialBlock, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
          Fintype.sum_sum_type, add_mul, mul_add, ite_mul, mul_ite,
          Fin.sum_univ_two, Finset.sum_add_distrib, hdiag] <;> grind only
    · simp [specialBlock, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fintype.sum_sum_type, add_mul, mul_add, ite_mul, mul_ite,
        Fin.sum_univ_two, Finset.sum_add_distrib, hdiag, hk]
  · fin_cases k <;>
      simp [specialBlock, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fintype.sum_sum_type, add_mul, mul_add, ite_mul, mul_ite,
        Fin.sum_univ_two, Finset.sum_add_distrib, hdiag] <;> grind only
  · fin_cases k <;> fin_cases j <;>
      simp [specialBlock, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fintype.sum_sum_type, add_mul, mul_add, ite_mul, mul_ite,
        Fin.sum_univ_two, Finset.sum_add_distrib, hdiag] <;> grind only

/-- The six-dimensional block, eight natural modules, and six fixed lines. -/
def blockMatrix (i : Fin 4) (A : SL(2, F)) : Matrix BlockIndex BlockIndex F :=
  Matrix.fromBlocks (specialBlock i A.1) 0 0
    (Matrix.fromBlocks (Matrix.blockDiagonal fun _ : Fin 8 => A.1) 0 0 1)

lemma blockMatrix_one (i : Fin 4) : blockMatrix i (1 : SL(2, F)) = 1 := by
  have h : Matrix.blockDiagonal (fun _ : Fin 8 => (1 : Matrix (Fin 2) (Fin 2) F)) = 1 :=
    Matrix.blockDiagonal_one
  simp only [blockMatrix, SpecialLinearGroup.coe_one, specialBlock_one, h,
    Matrix.fromBlocks_one]

lemma blockMatrix_mul (i : Fin 4) (A B : SL(2, F)) :
    blockMatrix i (A * B) = blockMatrix i A * blockMatrix i B := by
  unfold blockMatrix
  rw [specialBlock_mul]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, mul_one, SpecialLinearGroup.coe_mul,
    ← Matrix.blockDiagonal_mul]

/-- Faithfulness is visible on the first natural root-string block. -/
lemma blockMatrix_injective (i : Fin 4) : Function.Injective (blockMatrix (F := F) i) := by
  intro A B h
  apply Subtype.ext
  ext r s
  have hentry := congrArg
    (fun M : Matrix BlockIndex BlockIndex F => M (.inr (.inl (r, 0)))
      (.inr (.inl (s, 0)))) h
  simpa [blockMatrix, Matrix.blockDiagonal] using hentry

/-- A matrix monoid representation before restricting its range to the Geck group. -/
def blockHom (i : Fin 4) : SL(2, F) →* Matrix BlockIndex BlockIndex F where
  toFun := blockMatrix i
  map_one' := blockMatrix_one i
  map_mul' := blockMatrix_mul i

noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- The explicit faithful rank-one action on the actual Cartan-plus-root lattice. -/
def ambientHom (i : Fin 4) : SL(2, F) →* (Matrix LatticeIndex LatticeIndex F)ˣ :=
  ((Matrix.reindexAlgEquiv F F (latticeEquiv i)).toMonoidHom.comp (blockHom i)).toHomUnits

lemma ambientHom_injective (i : Fin 4) : Function.Injective (ambientHom (F := F) i) := by
  intro A B h
  apply blockMatrix_injective i
  apply (Matrix.reindexAlgEquiv F F (latticeEquiv i)).injective
  exact congrArg Units.val h

/-- Entrywise form of the action, without inverses of the coordinate equivalence. -/
lemma ambientHom_entry (i : Fin 4) (A : SL(2, F)) (r s : BlockIndex) :
    (ambientHom i A).val (latticeEquiv i r) (latticeEquiv i s) =
      blockMatrix i A r s := by
  simp [ambientHom, Matrix.reindexAlgEquiv, Matrix.reindexRingEquiv,
    Matrix.reindex_apply, blockHom]

/-- The remaining comparison with the integral Geck curves. The representation
and its injectivity are constructed above, not premises of this comparison. -/
structure CurveComparison : Prop where
  positive : ∀ i t, ambientHom (F := F) i
    (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t) =
      RootPairing.SimpleGeckGroup.positiveUnit
        (Theory.AlgebraicGroup.StandardRootSystem.typeDRootPairing_baseEquiv 2 i) t
  negative : ∀ i t, ambientHom (F := F) i
    (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t) =
      RootPairing.SimpleGeckGroup.negativeUnit
        (Theory.AlgebraicGroup.StandardRootSystem.typeDRootPairing_baseEquiv 2 i) t

end
end Triality.Standard.OddFundamentalCentralizer.RankOne
